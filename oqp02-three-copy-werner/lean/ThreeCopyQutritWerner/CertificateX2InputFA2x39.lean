module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [195, 200). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col195_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 0 v) = true := by decide +kernel
theorem col195_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 1 v) = true := by decide +kernel
theorem s195_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 0 = true := by decide +kernel
theorem s195_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 1 = true := by decide +kernel
theorem s195_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 2 = true := by decide +kernel
theorem s195_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 3 = true := by decide +kernel
theorem k195_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k195_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k195_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s195_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k195_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k195_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k195_2_4_80 k h.1 (by omega)
theorem s195_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 5 = true := by decide +kernel
theorem s195_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 6 = true := by decide +kernel
theorem s195_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 2 7 = true := by decide +kernel
theorem s195_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 0 = true := by decide +kernel
theorem s195_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 1 = true := by decide +kernel
theorem s195_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 2 = true := by decide +kernel
theorem s195_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 3 = true := by decide +kernel
theorem k195_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k195_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k195_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s195_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k195_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k195_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k195_3_4_80 k h.1 (by omega)
theorem s195_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 5 = true := by decide +kernel
theorem s195_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 6 = true := by decide +kernel
theorem s195_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 3 7 = true := by decide +kernel
theorem s195_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 0 = true := by decide +kernel
theorem s195_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 1 = true := by decide +kernel
theorem s195_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 2 = true := by decide +kernel
theorem s195_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 3 = true := by decide +kernel
theorem k195_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k195_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k195_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k195_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k195_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k195_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k195_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k195_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k195_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k195_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k195_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k195_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k195_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k195_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k195_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k195_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k195_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k195_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k195_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k195_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k195_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s195_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k195_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k195_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k195_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k195_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k195_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k195_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k195_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k195_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k195_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k195_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k195_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k195_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k195_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k195_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k195_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k195_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k195_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k195_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k195_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k195_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k195_4_4_100 k h.1 (by omega)
theorem k195_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k195_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k195_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k195_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k195_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k195_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k195_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k195_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k195_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s195_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k195_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k195_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k195_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k195_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k195_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k195_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k195_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k195_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k195_4_5_40 k h.1 (by omega)
theorem k195_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k195_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k195_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k195_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k195_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k195_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k195_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k195_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k195_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k195_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k195_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s195_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k195_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k195_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k195_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k195_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k195_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k195_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k195_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k195_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k195_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k195_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k195_4_6_50 k h.1 (by omega)
theorem s195_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 4 7 = true := by decide +kernel
theorem s195_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 0 = true := by decide +kernel
theorem s195_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 1 = true := by decide +kernel
theorem s195_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 2 = true := by decide +kernel
theorem s195_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 3 = true := by decide +kernel
theorem k195_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k195_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k195_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k195_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k195_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k195_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k195_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k195_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k195_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k195_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k195_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s195_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k195_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k195_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k195_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k195_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k195_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k195_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k195_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k195_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k195_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k195_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k195_5_4_100 k h.1 (by omega)
theorem k195_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k195_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k195_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k195_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k195_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s195_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k195_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k195_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k195_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k195_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k195_5_5_40 k h.1 (by omega)
theorem k195_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k195_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k195_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k195_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k195_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k195_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s195_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k195_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k195_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k195_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k195_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k195_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 195) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (195 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k195_5_6_50 k h.1 (by omega)
theorem s195_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 5 7 = true := by decide +kernel
theorem col195_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 6 v) = true := by decide +kernel
theorem col195_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 7 v) = true := by decide +kernel
theorem col195 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 195) 195 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col195_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col195_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s195_2_0
    · exact s195_2_1
    · exact s195_2_2
    · exact s195_2_3
    · exact s195_2_4
    · exact s195_2_5
    · exact s195_2_6
    · exact s195_2_7
  · fin_cases v
    · exact s195_3_0
    · exact s195_3_1
    · exact s195_3_2
    · exact s195_3_3
    · exact s195_3_4
    · exact s195_3_5
    · exact s195_3_6
    · exact s195_3_7
  · fin_cases v
    · exact s195_4_0
    · exact s195_4_1
    · exact s195_4_2
    · exact s195_4_3
    · exact s195_4_4
    · exact s195_4_5
    · exact s195_4_6
    · exact s195_4_7
  · fin_cases v
    · exact s195_5_0
    · exact s195_5_1
    · exact s195_5_2
    · exact s195_5_3
    · exact s195_5_4
    · exact s195_5_5
    · exact s195_5_6
    · exact s195_5_7
  · exact List.all_eq_true.mp col195_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col195_7 v (List.mem_finRange v)
theorem col196_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 0 v) = true := by decide +kernel
theorem col196_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 1 v) = true := by decide +kernel
theorem s196_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 0 = true := by decide +kernel
theorem s196_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 1 = true := by decide +kernel
theorem s196_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 2 = true := by decide +kernel
theorem s196_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 3 = true := by decide +kernel
theorem k196_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k196_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k196_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s196_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k196_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k196_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k196_2_4_80 k h.1 (by omega)
theorem s196_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 5 = true := by decide +kernel
theorem s196_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 6 = true := by decide +kernel
theorem s196_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 2 7 = true := by decide +kernel
theorem s196_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 0 = true := by decide +kernel
theorem s196_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 1 = true := by decide +kernel
theorem s196_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 2 = true := by decide +kernel
theorem s196_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 3 = true := by decide +kernel
theorem k196_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k196_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k196_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s196_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k196_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k196_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k196_3_4_80 k h.1 (by omega)
theorem s196_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 5 = true := by decide +kernel
theorem s196_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 6 = true := by decide +kernel
theorem s196_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 3 7 = true := by decide +kernel
theorem s196_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 0 = true := by decide +kernel
theorem s196_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 1 = true := by decide +kernel
theorem s196_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 2 = true := by decide +kernel
theorem s196_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 3 = true := by decide +kernel
theorem k196_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k196_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k196_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k196_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k196_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k196_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k196_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k196_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k196_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k196_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k196_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k196_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k196_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k196_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k196_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k196_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k196_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k196_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k196_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k196_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k196_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s196_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k196_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k196_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k196_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k196_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k196_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k196_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k196_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k196_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k196_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k196_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k196_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k196_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k196_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k196_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k196_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k196_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k196_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k196_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k196_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k196_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k196_4_4_100 k h.1 (by omega)
theorem k196_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k196_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k196_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k196_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k196_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k196_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k196_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k196_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k196_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s196_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k196_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k196_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k196_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k196_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k196_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k196_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k196_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k196_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k196_4_5_40 k h.1 (by omega)
theorem k196_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k196_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k196_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k196_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k196_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k196_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k196_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k196_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k196_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k196_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k196_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s196_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k196_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k196_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k196_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k196_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k196_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k196_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k196_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k196_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k196_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k196_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k196_4_6_50 k h.1 (by omega)
theorem s196_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 4 7 = true := by decide +kernel
theorem s196_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 0 = true := by decide +kernel
theorem s196_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 1 = true := by decide +kernel
theorem s196_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 2 = true := by decide +kernel
theorem s196_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 3 = true := by decide +kernel
theorem k196_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k196_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k196_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k196_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k196_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k196_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k196_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k196_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k196_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k196_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k196_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s196_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k196_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k196_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k196_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k196_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k196_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k196_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k196_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k196_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k196_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k196_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k196_5_4_100 k h.1 (by omega)
theorem k196_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k196_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k196_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k196_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k196_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s196_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k196_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k196_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k196_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k196_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k196_5_5_40 k h.1 (by omega)
theorem k196_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k196_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k196_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k196_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k196_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k196_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s196_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k196_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k196_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k196_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k196_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k196_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 196) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (196 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k196_5_6_50 k h.1 (by omega)
theorem s196_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 5 7 = true := by decide +kernel
theorem col196_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 6 v) = true := by decide +kernel
theorem col196_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 7 v) = true := by decide +kernel
theorem col196 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 196) 196 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col196_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col196_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s196_2_0
    · exact s196_2_1
    · exact s196_2_2
    · exact s196_2_3
    · exact s196_2_4
    · exact s196_2_5
    · exact s196_2_6
    · exact s196_2_7
  · fin_cases v
    · exact s196_3_0
    · exact s196_3_1
    · exact s196_3_2
    · exact s196_3_3
    · exact s196_3_4
    · exact s196_3_5
    · exact s196_3_6
    · exact s196_3_7
  · fin_cases v
    · exact s196_4_0
    · exact s196_4_1
    · exact s196_4_2
    · exact s196_4_3
    · exact s196_4_4
    · exact s196_4_5
    · exact s196_4_6
    · exact s196_4_7
  · fin_cases v
    · exact s196_5_0
    · exact s196_5_1
    · exact s196_5_2
    · exact s196_5_3
    · exact s196_5_4
    · exact s196_5_5
    · exact s196_5_6
    · exact s196_5_7
  · exact List.all_eq_true.mp col196_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col196_7 v (List.mem_finRange v)
theorem col197_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 0 v) = true := by decide +kernel
theorem col197_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 1 v) = true := by decide +kernel
theorem s197_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 0 = true := by decide +kernel
theorem s197_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 1 = true := by decide +kernel
theorem s197_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 2 = true := by decide +kernel
theorem s197_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 3 = true := by decide +kernel
theorem k197_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k197_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k197_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s197_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k197_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k197_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k197_2_4_80 k h.1 (by omega)
theorem s197_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 5 = true := by decide +kernel
theorem s197_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 6 = true := by decide +kernel
theorem s197_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 2 7 = true := by decide +kernel
theorem s197_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 0 = true := by decide +kernel
theorem s197_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 1 = true := by decide +kernel
theorem s197_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 2 = true := by decide +kernel
theorem s197_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 3 = true := by decide +kernel
theorem k197_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k197_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k197_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s197_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k197_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k197_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k197_3_4_80 k h.1 (by omega)
theorem s197_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 5 = true := by decide +kernel
theorem s197_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 6 = true := by decide +kernel
theorem s197_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 3 7 = true := by decide +kernel
theorem s197_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 0 = true := by decide +kernel
theorem s197_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 1 = true := by decide +kernel
theorem s197_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 2 = true := by decide +kernel
theorem s197_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 3 = true := by decide +kernel
theorem k197_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k197_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k197_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k197_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k197_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k197_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k197_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k197_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k197_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k197_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k197_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k197_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k197_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k197_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k197_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k197_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k197_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k197_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k197_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k197_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k197_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s197_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k197_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k197_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k197_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k197_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k197_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k197_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k197_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k197_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k197_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k197_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k197_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k197_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k197_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k197_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k197_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k197_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k197_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k197_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k197_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k197_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k197_4_4_100 k h.1 (by omega)
theorem k197_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k197_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k197_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k197_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k197_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k197_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k197_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k197_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k197_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s197_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k197_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k197_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k197_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k197_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k197_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k197_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k197_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k197_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k197_4_5_40 k h.1 (by omega)
theorem k197_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k197_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k197_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k197_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k197_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k197_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k197_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k197_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k197_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k197_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k197_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s197_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k197_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k197_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k197_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k197_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k197_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k197_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k197_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k197_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k197_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k197_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k197_4_6_50 k h.1 (by omega)
theorem s197_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 4 7 = true := by decide +kernel
theorem s197_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 0 = true := by decide +kernel
theorem s197_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 1 = true := by decide +kernel
theorem s197_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 2 = true := by decide +kernel
theorem s197_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 3 = true := by decide +kernel
theorem k197_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k197_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k197_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k197_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k197_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k197_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k197_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k197_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k197_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k197_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k197_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s197_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k197_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k197_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k197_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k197_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k197_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k197_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k197_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k197_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k197_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k197_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k197_5_4_100 k h.1 (by omega)
theorem k197_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k197_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k197_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k197_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k197_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s197_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k197_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k197_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k197_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k197_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k197_5_5_40 k h.1 (by omega)
theorem k197_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k197_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k197_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k197_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k197_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k197_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s197_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k197_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k197_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k197_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k197_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k197_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 197) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (197 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k197_5_6_50 k h.1 (by omega)
theorem s197_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 5 7 = true := by decide +kernel
theorem col197_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 6 v) = true := by decide +kernel
theorem col197_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 7 v) = true := by decide +kernel
theorem col197 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 197) 197 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col197_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col197_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s197_2_0
    · exact s197_2_1
    · exact s197_2_2
    · exact s197_2_3
    · exact s197_2_4
    · exact s197_2_5
    · exact s197_2_6
    · exact s197_2_7
  · fin_cases v
    · exact s197_3_0
    · exact s197_3_1
    · exact s197_3_2
    · exact s197_3_3
    · exact s197_3_4
    · exact s197_3_5
    · exact s197_3_6
    · exact s197_3_7
  · fin_cases v
    · exact s197_4_0
    · exact s197_4_1
    · exact s197_4_2
    · exact s197_4_3
    · exact s197_4_4
    · exact s197_4_5
    · exact s197_4_6
    · exact s197_4_7
  · fin_cases v
    · exact s197_5_0
    · exact s197_5_1
    · exact s197_5_2
    · exact s197_5_3
    · exact s197_5_4
    · exact s197_5_5
    · exact s197_5_6
    · exact s197_5_7
  · exact List.all_eq_true.mp col197_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col197_7 v (List.mem_finRange v)
theorem col198_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 0 v) = true := by decide +kernel
theorem col198_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 1 v) = true := by decide +kernel
theorem s198_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 0 = true := by decide +kernel
theorem s198_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 1 = true := by decide +kernel
theorem s198_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 2 = true := by decide +kernel
theorem s198_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 3 = true := by decide +kernel
theorem k198_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k198_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k198_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s198_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k198_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k198_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k198_2_4_80 k h.1 (by omega)
theorem s198_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 5 = true := by decide +kernel
theorem s198_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 6 = true := by decide +kernel
theorem s198_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 2 7 = true := by decide +kernel
theorem s198_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 0 = true := by decide +kernel
theorem s198_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 1 = true := by decide +kernel
theorem s198_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 2 = true := by decide +kernel
theorem s198_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 3 = true := by decide +kernel
theorem k198_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k198_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k198_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s198_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k198_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k198_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k198_3_4_80 k h.1 (by omega)
theorem s198_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 5 = true := by decide +kernel
theorem s198_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 6 = true := by decide +kernel
theorem s198_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 3 7 = true := by decide +kernel
theorem s198_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 0 = true := by decide +kernel
theorem s198_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 1 = true := by decide +kernel
theorem s198_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 2 = true := by decide +kernel
theorem s198_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 3 = true := by decide +kernel
theorem k198_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k198_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k198_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k198_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k198_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k198_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k198_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k198_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k198_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k198_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k198_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k198_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k198_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k198_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k198_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k198_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k198_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k198_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k198_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k198_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k198_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s198_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k198_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k198_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k198_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k198_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k198_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k198_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k198_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k198_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k198_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k198_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k198_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k198_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k198_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k198_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k198_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k198_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k198_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k198_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k198_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k198_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k198_4_4_100 k h.1 (by omega)
theorem k198_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k198_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k198_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k198_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k198_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k198_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k198_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k198_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k198_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s198_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k198_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k198_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k198_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k198_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k198_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k198_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k198_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k198_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k198_4_5_40 k h.1 (by omega)
theorem k198_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k198_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k198_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k198_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k198_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k198_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k198_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k198_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k198_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k198_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k198_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s198_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k198_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k198_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k198_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k198_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k198_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k198_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k198_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k198_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k198_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k198_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k198_4_6_50 k h.1 (by omega)
theorem s198_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 4 7 = true := by decide +kernel
theorem s198_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 0 = true := by decide +kernel
theorem s198_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 1 = true := by decide +kernel
theorem s198_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 2 = true := by decide +kernel
theorem s198_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 3 = true := by decide +kernel
theorem k198_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k198_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k198_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k198_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k198_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k198_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k198_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k198_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k198_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k198_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k198_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s198_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k198_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k198_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k198_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k198_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k198_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k198_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k198_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k198_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k198_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k198_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k198_5_4_100 k h.1 (by omega)
theorem k198_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k198_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k198_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k198_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k198_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s198_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k198_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k198_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k198_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k198_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k198_5_5_40 k h.1 (by omega)
theorem k198_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k198_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k198_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k198_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k198_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k198_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s198_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k198_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k198_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k198_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k198_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k198_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 198) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (198 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k198_5_6_50 k h.1 (by omega)
theorem s198_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 5 7 = true := by decide +kernel
theorem col198_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 6 v) = true := by decide +kernel
theorem col198_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 7 v) = true := by decide +kernel
theorem col198 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 198) 198 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col198_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col198_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s198_2_0
    · exact s198_2_1
    · exact s198_2_2
    · exact s198_2_3
    · exact s198_2_4
    · exact s198_2_5
    · exact s198_2_6
    · exact s198_2_7
  · fin_cases v
    · exact s198_3_0
    · exact s198_3_1
    · exact s198_3_2
    · exact s198_3_3
    · exact s198_3_4
    · exact s198_3_5
    · exact s198_3_6
    · exact s198_3_7
  · fin_cases v
    · exact s198_4_0
    · exact s198_4_1
    · exact s198_4_2
    · exact s198_4_3
    · exact s198_4_4
    · exact s198_4_5
    · exact s198_4_6
    · exact s198_4_7
  · fin_cases v
    · exact s198_5_0
    · exact s198_5_1
    · exact s198_5_2
    · exact s198_5_3
    · exact s198_5_4
    · exact s198_5_5
    · exact s198_5_6
    · exact s198_5_7
  · exact List.all_eq_true.mp col198_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col198_7 v (List.mem_finRange v)
theorem col199_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 0 v) = true := by decide +kernel
theorem col199_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 1 v) = true := by decide +kernel
theorem s199_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 0 = true := by decide +kernel
theorem s199_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 1 = true := by decide +kernel
theorem s199_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 2 = true := by decide +kernel
theorem s199_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 3 = true := by decide +kernel
theorem k199_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k199_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k199_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s199_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k199_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k199_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k199_2_4_80 k h.1 (by omega)
theorem s199_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 5 = true := by decide +kernel
theorem s199_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 6 = true := by decide +kernel
theorem s199_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 2 7 = true := by decide +kernel
theorem s199_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 0 = true := by decide +kernel
theorem s199_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 1 = true := by decide +kernel
theorem s199_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 2 = true := by decide +kernel
theorem s199_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 3 = true := by decide +kernel
theorem k199_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k199_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k199_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s199_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k199_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k199_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k199_3_4_80 k h.1 (by omega)
theorem s199_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 5 = true := by decide +kernel
theorem s199_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 6 = true := by decide +kernel
theorem s199_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 3 7 = true := by decide +kernel
theorem s199_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 0 = true := by decide +kernel
theorem s199_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 1 = true := by decide +kernel
theorem s199_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 2 = true := by decide +kernel
theorem s199_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 3 = true := by decide +kernel
theorem k199_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k199_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k199_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k199_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k199_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k199_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k199_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k199_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k199_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k199_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k199_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k199_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k199_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k199_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k199_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k199_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k199_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k199_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k199_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k199_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k199_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s199_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k199_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k199_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k199_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k199_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k199_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k199_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k199_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k199_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k199_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k199_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k199_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k199_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k199_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k199_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k199_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k199_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k199_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k199_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k199_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k199_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k199_4_4_100 k h.1 (by omega)
theorem k199_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k199_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k199_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k199_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k199_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k199_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k199_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k199_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k199_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s199_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k199_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k199_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k199_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k199_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k199_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k199_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k199_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k199_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k199_4_5_40 k h.1 (by omega)
theorem k199_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k199_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k199_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k199_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k199_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k199_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k199_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k199_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k199_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k199_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k199_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s199_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k199_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k199_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k199_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k199_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k199_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k199_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k199_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k199_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k199_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k199_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k199_4_6_50 k h.1 (by omega)
theorem s199_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 4 7 = true := by decide +kernel
theorem s199_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 0 = true := by decide +kernel
theorem s199_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 1 = true := by decide +kernel
theorem s199_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 2 = true := by decide +kernel
theorem s199_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 3 = true := by decide +kernel
theorem k199_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k199_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k199_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k199_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k199_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k199_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k199_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k199_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k199_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k199_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k199_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s199_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k199_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k199_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k199_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k199_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k199_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k199_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k199_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k199_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k199_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k199_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k199_5_4_100 k h.1 (by omega)
theorem k199_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k199_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k199_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k199_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k199_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s199_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k199_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k199_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k199_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k199_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k199_5_5_40 k h.1 (by omega)
theorem k199_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k199_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k199_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k199_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k199_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k199_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s199_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k199_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k199_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k199_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k199_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k199_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 199) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (199 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k199_5_6_50 k h.1 (by omega)
theorem s199_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 5 7 = true := by decide +kernel
theorem col199_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 6 v) = true := by decide +kernel
theorem col199_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 7 v) = true := by decide +kernel
theorem col199 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 199) 199 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col199_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col199_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s199_2_0
    · exact s199_2_1
    · exact s199_2_2
    · exact s199_2_3
    · exact s199_2_4
    · exact s199_2_5
    · exact s199_2_6
    · exact s199_2_7
  · fin_cases v
    · exact s199_3_0
    · exact s199_3_1
    · exact s199_3_2
    · exact s199_3_3
    · exact s199_3_4
    · exact s199_3_5
    · exact s199_3_6
    · exact s199_3_7
  · fin_cases v
    · exact s199_4_0
    · exact s199_4_1
    · exact s199_4_2
    · exact s199_4_3
    · exact s199_4_4
    · exact s199_4_5
    · exact s199_4_6
    · exact s199_4_7
  · fin_cases v
    · exact s199_5_0
    · exact s199_5_1
    · exact s199_5_2
    · exact s199_5_3
    · exact s199_5_4
    · exact s199_5_5
    · exact s199_5_6
    · exact s199_5_7
  · exact List.all_eq_true.mp col199_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col199_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
