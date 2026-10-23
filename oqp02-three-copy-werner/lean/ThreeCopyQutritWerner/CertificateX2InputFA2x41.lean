module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [205, 210). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col205_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 0 v) = true := by decide +kernel
theorem col205_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 1 v) = true := by decide +kernel
theorem s205_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 0 = true := by decide +kernel
theorem s205_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 1 = true := by decide +kernel
theorem s205_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 2 = true := by decide +kernel
theorem s205_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 3 = true := by decide +kernel
theorem k205_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k205_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k205_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s205_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k205_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k205_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k205_2_4_80 k h.1 (by omega)
theorem s205_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 5 = true := by decide +kernel
theorem s205_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 6 = true := by decide +kernel
theorem s205_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 2 7 = true := by decide +kernel
theorem s205_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 0 = true := by decide +kernel
theorem s205_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 1 = true := by decide +kernel
theorem s205_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 2 = true := by decide +kernel
theorem s205_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 3 = true := by decide +kernel
theorem k205_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k205_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k205_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s205_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k205_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k205_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k205_3_4_80 k h.1 (by omega)
theorem s205_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 5 = true := by decide +kernel
theorem s205_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 6 = true := by decide +kernel
theorem s205_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 3 7 = true := by decide +kernel
theorem s205_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 0 = true := by decide +kernel
theorem s205_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 1 = true := by decide +kernel
theorem s205_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 2 = true := by decide +kernel
theorem s205_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 3 = true := by decide +kernel
theorem k205_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k205_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k205_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k205_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k205_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k205_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k205_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k205_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k205_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k205_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k205_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k205_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k205_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k205_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k205_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k205_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k205_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k205_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k205_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k205_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k205_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s205_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k205_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k205_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k205_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k205_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k205_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k205_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k205_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k205_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k205_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k205_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k205_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k205_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k205_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k205_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k205_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k205_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k205_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k205_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k205_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k205_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k205_4_4_100 k h.1 (by omega)
theorem k205_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k205_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k205_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k205_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k205_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k205_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k205_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k205_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k205_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s205_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k205_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k205_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k205_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k205_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k205_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k205_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k205_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k205_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k205_4_5_40 k h.1 (by omega)
theorem k205_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k205_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k205_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k205_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k205_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k205_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k205_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k205_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k205_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k205_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k205_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s205_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k205_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k205_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k205_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k205_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k205_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k205_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k205_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k205_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k205_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k205_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k205_4_6_50 k h.1 (by omega)
theorem s205_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 4 7 = true := by decide +kernel
theorem s205_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 0 = true := by decide +kernel
theorem s205_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 1 = true := by decide +kernel
theorem s205_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 2 = true := by decide +kernel
theorem s205_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 3 = true := by decide +kernel
theorem k205_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k205_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k205_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k205_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k205_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k205_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k205_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k205_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k205_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k205_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k205_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s205_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k205_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k205_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k205_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k205_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k205_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k205_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k205_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k205_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k205_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k205_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k205_5_4_100 k h.1 (by omega)
theorem k205_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k205_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k205_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k205_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k205_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s205_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k205_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k205_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k205_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k205_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k205_5_5_40 k h.1 (by omega)
theorem k205_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k205_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k205_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k205_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k205_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k205_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s205_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k205_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k205_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k205_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k205_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k205_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 205) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (205 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k205_5_6_50 k h.1 (by omega)
theorem s205_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 5 7 = true := by decide +kernel
theorem col205_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 6 v) = true := by decide +kernel
theorem col205_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 7 v) = true := by decide +kernel
theorem col205 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 205) 205 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col205_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col205_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s205_2_0
    · exact s205_2_1
    · exact s205_2_2
    · exact s205_2_3
    · exact s205_2_4
    · exact s205_2_5
    · exact s205_2_6
    · exact s205_2_7
  · fin_cases v
    · exact s205_3_0
    · exact s205_3_1
    · exact s205_3_2
    · exact s205_3_3
    · exact s205_3_4
    · exact s205_3_5
    · exact s205_3_6
    · exact s205_3_7
  · fin_cases v
    · exact s205_4_0
    · exact s205_4_1
    · exact s205_4_2
    · exact s205_4_3
    · exact s205_4_4
    · exact s205_4_5
    · exact s205_4_6
    · exact s205_4_7
  · fin_cases v
    · exact s205_5_0
    · exact s205_5_1
    · exact s205_5_2
    · exact s205_5_3
    · exact s205_5_4
    · exact s205_5_5
    · exact s205_5_6
    · exact s205_5_7
  · exact List.all_eq_true.mp col205_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col205_7 v (List.mem_finRange v)
theorem col206_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 0 v) = true := by decide +kernel
theorem col206_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 1 v) = true := by decide +kernel
theorem s206_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 0 = true := by decide +kernel
theorem s206_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 1 = true := by decide +kernel
theorem s206_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 2 = true := by decide +kernel
theorem s206_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 3 = true := by decide +kernel
theorem k206_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k206_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k206_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s206_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k206_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k206_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k206_2_4_80 k h.1 (by omega)
theorem s206_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 5 = true := by decide +kernel
theorem s206_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 6 = true := by decide +kernel
theorem s206_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 2 7 = true := by decide +kernel
theorem s206_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 0 = true := by decide +kernel
theorem s206_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 1 = true := by decide +kernel
theorem s206_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 2 = true := by decide +kernel
theorem s206_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 3 = true := by decide +kernel
theorem k206_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k206_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k206_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s206_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k206_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k206_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k206_3_4_80 k h.1 (by omega)
theorem s206_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 5 = true := by decide +kernel
theorem s206_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 6 = true := by decide +kernel
theorem s206_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 3 7 = true := by decide +kernel
theorem s206_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 0 = true := by decide +kernel
theorem s206_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 1 = true := by decide +kernel
theorem s206_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 2 = true := by decide +kernel
theorem s206_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 3 = true := by decide +kernel
theorem k206_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k206_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k206_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k206_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k206_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k206_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k206_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k206_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k206_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k206_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k206_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k206_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k206_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k206_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k206_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k206_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k206_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k206_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k206_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k206_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k206_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s206_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k206_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k206_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k206_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k206_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k206_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k206_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k206_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k206_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k206_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k206_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k206_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k206_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k206_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k206_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k206_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k206_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k206_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k206_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k206_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k206_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k206_4_4_100 k h.1 (by omega)
theorem k206_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k206_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k206_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k206_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k206_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k206_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k206_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k206_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k206_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s206_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k206_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k206_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k206_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k206_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k206_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k206_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k206_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k206_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k206_4_5_40 k h.1 (by omega)
theorem k206_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k206_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k206_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k206_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k206_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k206_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k206_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k206_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k206_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k206_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k206_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s206_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k206_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k206_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k206_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k206_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k206_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k206_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k206_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k206_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k206_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k206_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k206_4_6_50 k h.1 (by omega)
theorem s206_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 4 7 = true := by decide +kernel
theorem s206_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 0 = true := by decide +kernel
theorem s206_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 1 = true := by decide +kernel
theorem s206_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 2 = true := by decide +kernel
theorem s206_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 3 = true := by decide +kernel
theorem k206_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k206_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k206_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k206_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k206_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k206_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k206_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k206_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k206_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k206_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k206_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s206_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k206_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k206_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k206_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k206_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k206_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k206_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k206_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k206_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k206_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k206_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k206_5_4_100 k h.1 (by omega)
theorem k206_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k206_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k206_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k206_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k206_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s206_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k206_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k206_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k206_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k206_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k206_5_5_40 k h.1 (by omega)
theorem k206_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k206_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k206_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k206_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k206_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k206_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s206_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k206_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k206_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k206_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k206_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k206_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 206) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (206 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k206_5_6_50 k h.1 (by omega)
theorem s206_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 5 7 = true := by decide +kernel
theorem col206_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 6 v) = true := by decide +kernel
theorem col206_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 7 v) = true := by decide +kernel
theorem col206 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 206) 206 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col206_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col206_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s206_2_0
    · exact s206_2_1
    · exact s206_2_2
    · exact s206_2_3
    · exact s206_2_4
    · exact s206_2_5
    · exact s206_2_6
    · exact s206_2_7
  · fin_cases v
    · exact s206_3_0
    · exact s206_3_1
    · exact s206_3_2
    · exact s206_3_3
    · exact s206_3_4
    · exact s206_3_5
    · exact s206_3_6
    · exact s206_3_7
  · fin_cases v
    · exact s206_4_0
    · exact s206_4_1
    · exact s206_4_2
    · exact s206_4_3
    · exact s206_4_4
    · exact s206_4_5
    · exact s206_4_6
    · exact s206_4_7
  · fin_cases v
    · exact s206_5_0
    · exact s206_5_1
    · exact s206_5_2
    · exact s206_5_3
    · exact s206_5_4
    · exact s206_5_5
    · exact s206_5_6
    · exact s206_5_7
  · exact List.all_eq_true.mp col206_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col206_7 v (List.mem_finRange v)
theorem col207_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 0 v) = true := by decide +kernel
theorem col207_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 1 v) = true := by decide +kernel
theorem s207_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 0 = true := by decide +kernel
theorem s207_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 1 = true := by decide +kernel
theorem s207_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 2 = true := by decide +kernel
theorem s207_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 3 = true := by decide +kernel
theorem k207_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k207_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k207_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s207_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k207_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k207_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k207_2_4_80 k h.1 (by omega)
theorem s207_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 5 = true := by decide +kernel
theorem s207_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 6 = true := by decide +kernel
theorem s207_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 2 7 = true := by decide +kernel
theorem s207_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 0 = true := by decide +kernel
theorem s207_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 1 = true := by decide +kernel
theorem s207_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 2 = true := by decide +kernel
theorem s207_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 3 = true := by decide +kernel
theorem k207_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k207_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k207_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s207_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k207_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k207_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k207_3_4_80 k h.1 (by omega)
theorem s207_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 5 = true := by decide +kernel
theorem s207_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 6 = true := by decide +kernel
theorem s207_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 3 7 = true := by decide +kernel
theorem s207_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 0 = true := by decide +kernel
theorem s207_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 1 = true := by decide +kernel
theorem s207_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 2 = true := by decide +kernel
theorem s207_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 3 = true := by decide +kernel
theorem k207_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k207_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k207_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k207_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k207_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k207_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k207_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k207_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k207_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k207_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k207_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k207_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k207_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k207_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k207_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k207_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k207_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k207_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k207_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k207_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k207_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s207_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k207_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k207_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k207_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k207_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k207_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k207_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k207_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k207_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k207_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k207_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k207_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k207_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k207_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k207_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k207_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k207_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k207_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k207_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k207_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k207_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k207_4_4_100 k h.1 (by omega)
theorem k207_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k207_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k207_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k207_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k207_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k207_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k207_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k207_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k207_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s207_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k207_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k207_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k207_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k207_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k207_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k207_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k207_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k207_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k207_4_5_40 k h.1 (by omega)
theorem k207_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k207_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k207_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k207_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k207_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k207_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k207_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k207_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k207_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k207_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k207_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s207_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k207_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k207_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k207_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k207_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k207_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k207_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k207_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k207_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k207_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k207_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k207_4_6_50 k h.1 (by omega)
theorem s207_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 4 7 = true := by decide +kernel
theorem s207_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 0 = true := by decide +kernel
theorem s207_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 1 = true := by decide +kernel
theorem s207_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 2 = true := by decide +kernel
theorem s207_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 3 = true := by decide +kernel
theorem k207_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k207_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k207_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k207_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k207_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k207_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k207_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k207_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k207_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k207_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k207_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s207_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k207_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k207_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k207_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k207_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k207_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k207_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k207_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k207_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k207_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k207_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k207_5_4_100 k h.1 (by omega)
theorem k207_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k207_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k207_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k207_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k207_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s207_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k207_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k207_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k207_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k207_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k207_5_5_40 k h.1 (by omega)
theorem k207_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k207_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k207_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k207_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k207_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k207_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s207_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k207_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k207_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k207_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k207_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k207_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 207) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (207 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k207_5_6_50 k h.1 (by omega)
theorem s207_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 5 7 = true := by decide +kernel
theorem col207_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 6 v) = true := by decide +kernel
theorem col207_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 7 v) = true := by decide +kernel
theorem col207 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 207) 207 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col207_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col207_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s207_2_0
    · exact s207_2_1
    · exact s207_2_2
    · exact s207_2_3
    · exact s207_2_4
    · exact s207_2_5
    · exact s207_2_6
    · exact s207_2_7
  · fin_cases v
    · exact s207_3_0
    · exact s207_3_1
    · exact s207_3_2
    · exact s207_3_3
    · exact s207_3_4
    · exact s207_3_5
    · exact s207_3_6
    · exact s207_3_7
  · fin_cases v
    · exact s207_4_0
    · exact s207_4_1
    · exact s207_4_2
    · exact s207_4_3
    · exact s207_4_4
    · exact s207_4_5
    · exact s207_4_6
    · exact s207_4_7
  · fin_cases v
    · exact s207_5_0
    · exact s207_5_1
    · exact s207_5_2
    · exact s207_5_3
    · exact s207_5_4
    · exact s207_5_5
    · exact s207_5_6
    · exact s207_5_7
  · exact List.all_eq_true.mp col207_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col207_7 v (List.mem_finRange v)
theorem col208_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 0 v) = true := by decide +kernel
theorem col208_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 1 v) = true := by decide +kernel
theorem s208_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 0 = true := by decide +kernel
theorem s208_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 1 = true := by decide +kernel
theorem s208_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 2 = true := by decide +kernel
theorem s208_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 3 = true := by decide +kernel
theorem k208_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k208_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k208_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s208_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k208_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k208_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k208_2_4_80 k h.1 (by omega)
theorem s208_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 5 = true := by decide +kernel
theorem s208_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 6 = true := by decide +kernel
theorem s208_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 2 7 = true := by decide +kernel
theorem s208_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 0 = true := by decide +kernel
theorem s208_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 1 = true := by decide +kernel
theorem s208_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 2 = true := by decide +kernel
theorem s208_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 3 = true := by decide +kernel
theorem k208_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k208_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k208_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s208_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k208_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k208_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k208_3_4_80 k h.1 (by omega)
theorem s208_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 5 = true := by decide +kernel
theorem s208_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 6 = true := by decide +kernel
theorem s208_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 3 7 = true := by decide +kernel
theorem s208_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 0 = true := by decide +kernel
theorem s208_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 1 = true := by decide +kernel
theorem s208_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 2 = true := by decide +kernel
theorem s208_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 3 = true := by decide +kernel
theorem k208_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k208_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k208_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k208_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k208_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k208_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k208_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k208_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k208_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k208_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k208_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k208_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k208_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k208_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k208_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k208_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k208_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k208_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k208_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k208_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k208_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s208_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k208_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k208_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k208_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k208_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k208_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k208_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k208_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k208_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k208_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k208_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k208_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k208_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k208_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k208_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k208_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k208_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k208_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k208_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k208_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k208_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k208_4_4_100 k h.1 (by omega)
theorem k208_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k208_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k208_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k208_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k208_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k208_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k208_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k208_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k208_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s208_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k208_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k208_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k208_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k208_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k208_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k208_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k208_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k208_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k208_4_5_40 k h.1 (by omega)
theorem k208_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k208_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k208_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k208_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k208_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k208_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k208_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k208_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k208_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k208_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k208_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s208_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k208_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k208_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k208_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k208_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k208_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k208_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k208_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k208_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k208_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k208_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k208_4_6_50 k h.1 (by omega)
theorem s208_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 4 7 = true := by decide +kernel
theorem s208_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 0 = true := by decide +kernel
theorem s208_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 1 = true := by decide +kernel
theorem s208_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 2 = true := by decide +kernel
theorem s208_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 3 = true := by decide +kernel
theorem k208_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k208_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k208_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k208_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k208_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k208_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k208_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k208_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k208_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k208_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k208_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s208_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k208_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k208_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k208_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k208_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k208_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k208_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k208_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k208_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k208_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k208_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k208_5_4_100 k h.1 (by omega)
theorem k208_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k208_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k208_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k208_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k208_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s208_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k208_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k208_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k208_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k208_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k208_5_5_40 k h.1 (by omega)
theorem k208_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k208_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k208_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k208_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k208_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k208_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s208_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k208_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k208_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k208_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k208_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k208_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 208) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (208 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k208_5_6_50 k h.1 (by omega)
theorem s208_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 5 7 = true := by decide +kernel
theorem col208_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 6 v) = true := by decide +kernel
theorem col208_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 7 v) = true := by decide +kernel
theorem col208 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 208) 208 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col208_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col208_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s208_2_0
    · exact s208_2_1
    · exact s208_2_2
    · exact s208_2_3
    · exact s208_2_4
    · exact s208_2_5
    · exact s208_2_6
    · exact s208_2_7
  · fin_cases v
    · exact s208_3_0
    · exact s208_3_1
    · exact s208_3_2
    · exact s208_3_3
    · exact s208_3_4
    · exact s208_3_5
    · exact s208_3_6
    · exact s208_3_7
  · fin_cases v
    · exact s208_4_0
    · exact s208_4_1
    · exact s208_4_2
    · exact s208_4_3
    · exact s208_4_4
    · exact s208_4_5
    · exact s208_4_6
    · exact s208_4_7
  · fin_cases v
    · exact s208_5_0
    · exact s208_5_1
    · exact s208_5_2
    · exact s208_5_3
    · exact s208_5_4
    · exact s208_5_5
    · exact s208_5_6
    · exact s208_5_7
  · exact List.all_eq_true.mp col208_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col208_7 v (List.mem_finRange v)
theorem col209_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 0 v) = true := by decide +kernel
theorem col209_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 1 v) = true := by decide +kernel
theorem s209_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 0 = true := by decide +kernel
theorem s209_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 1 = true := by decide +kernel
theorem s209_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 2 = true := by decide +kernel
theorem s209_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 3 = true := by decide +kernel
theorem k209_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k209_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k209_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s209_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k209_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k209_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k209_2_4_80 k h.1 (by omega)
theorem s209_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 5 = true := by decide +kernel
theorem s209_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 6 = true := by decide +kernel
theorem s209_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 2 7 = true := by decide +kernel
theorem s209_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 0 = true := by decide +kernel
theorem s209_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 1 = true := by decide +kernel
theorem s209_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 2 = true := by decide +kernel
theorem s209_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 3 = true := by decide +kernel
theorem k209_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k209_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k209_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s209_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k209_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k209_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k209_3_4_80 k h.1 (by omega)
theorem s209_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 5 = true := by decide +kernel
theorem s209_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 6 = true := by decide +kernel
theorem s209_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 3 7 = true := by decide +kernel
theorem s209_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 0 = true := by decide +kernel
theorem s209_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 1 = true := by decide +kernel
theorem s209_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 2 = true := by decide +kernel
theorem s209_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 3 = true := by decide +kernel
theorem k209_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k209_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k209_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k209_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k209_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k209_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k209_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k209_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k209_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k209_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k209_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k209_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k209_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k209_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k209_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k209_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k209_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k209_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k209_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k209_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k209_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s209_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k209_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k209_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k209_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k209_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k209_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k209_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k209_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k209_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k209_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k209_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k209_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k209_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k209_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k209_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k209_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k209_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k209_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k209_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k209_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k209_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k209_4_4_100 k h.1 (by omega)
theorem k209_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k209_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k209_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k209_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k209_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k209_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k209_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k209_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k209_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s209_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k209_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k209_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k209_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k209_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k209_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k209_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k209_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k209_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k209_4_5_40 k h.1 (by omega)
theorem k209_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k209_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k209_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k209_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k209_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k209_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k209_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k209_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k209_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k209_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k209_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s209_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k209_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k209_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k209_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k209_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k209_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k209_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k209_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k209_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k209_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k209_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k209_4_6_50 k h.1 (by omega)
theorem s209_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 4 7 = true := by decide +kernel
theorem s209_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 0 = true := by decide +kernel
theorem s209_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 1 = true := by decide +kernel
theorem s209_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 2 = true := by decide +kernel
theorem s209_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 3 = true := by decide +kernel
theorem k209_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k209_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k209_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k209_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k209_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k209_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k209_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k209_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k209_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k209_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k209_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s209_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k209_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k209_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k209_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k209_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k209_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k209_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k209_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k209_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k209_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k209_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k209_5_4_100 k h.1 (by omega)
theorem k209_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k209_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k209_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k209_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k209_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s209_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k209_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k209_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k209_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k209_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k209_5_5_40 k h.1 (by omega)
theorem k209_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k209_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k209_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k209_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k209_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k209_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s209_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k209_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k209_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k209_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k209_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k209_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 209) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (209 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k209_5_6_50 k h.1 (by omega)
theorem s209_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 5 7 = true := by decide +kernel
theorem col209_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 6 v) = true := by decide +kernel
theorem col209_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 7 v) = true := by decide +kernel
theorem col209 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 209) 209 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col209_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col209_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s209_2_0
    · exact s209_2_1
    · exact s209_2_2
    · exact s209_2_3
    · exact s209_2_4
    · exact s209_2_5
    · exact s209_2_6
    · exact s209_2_7
  · fin_cases v
    · exact s209_3_0
    · exact s209_3_1
    · exact s209_3_2
    · exact s209_3_3
    · exact s209_3_4
    · exact s209_3_5
    · exact s209_3_6
    · exact s209_3_7
  · fin_cases v
    · exact s209_4_0
    · exact s209_4_1
    · exact s209_4_2
    · exact s209_4_3
    · exact s209_4_4
    · exact s209_4_5
    · exact s209_4_6
    · exact s209_4_7
  · fin_cases v
    · exact s209_5_0
    · exact s209_5_1
    · exact s209_5_2
    · exact s209_5_3
    · exact s209_5_4
    · exact s209_5_5
    · exact s209_5_6
    · exact s209_5_7
  · exact List.all_eq_true.mp col209_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col209_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
