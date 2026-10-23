module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [145, 150). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col145_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 0 v) = true := by decide +kernel
theorem col145_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 1 v) = true := by decide +kernel
theorem s145_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 0 = true := by decide +kernel
theorem s145_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 1 = true := by decide +kernel
theorem s145_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 2 = true := by decide +kernel
theorem s145_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 3 = true := by decide +kernel
theorem k145_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k145_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k145_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s145_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k145_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k145_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k145_2_4_80 k h.1 (by omega)
theorem s145_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 5 = true := by decide +kernel
theorem s145_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 6 = true := by decide +kernel
theorem s145_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 2 7 = true := by decide +kernel
theorem s145_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 0 = true := by decide +kernel
theorem s145_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 1 = true := by decide +kernel
theorem s145_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 2 = true := by decide +kernel
theorem s145_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 3 = true := by decide +kernel
theorem k145_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k145_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k145_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s145_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k145_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k145_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k145_3_4_80 k h.1 (by omega)
theorem s145_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 5 = true := by decide +kernel
theorem s145_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 6 = true := by decide +kernel
theorem s145_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 3 7 = true := by decide +kernel
theorem s145_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 0 = true := by decide +kernel
theorem s145_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 1 = true := by decide +kernel
theorem s145_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 2 = true := by decide +kernel
theorem s145_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 3 = true := by decide +kernel
theorem k145_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k145_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k145_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k145_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k145_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k145_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k145_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k145_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k145_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k145_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k145_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k145_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k145_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k145_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k145_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k145_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k145_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k145_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k145_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k145_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k145_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s145_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k145_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k145_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k145_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k145_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k145_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k145_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k145_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k145_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k145_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k145_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k145_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k145_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k145_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k145_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k145_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k145_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k145_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k145_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k145_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k145_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k145_4_4_100 k h.1 (by omega)
theorem k145_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k145_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k145_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k145_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k145_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k145_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k145_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k145_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k145_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s145_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k145_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k145_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k145_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k145_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k145_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k145_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k145_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k145_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 145) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (145 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k145_4_5_40 k h.1 (by omega)
theorem k145_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k145_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k145_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k145_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k145_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k145_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k145_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k145_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k145_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k145_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k145_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s145_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k145_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k145_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k145_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k145_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k145_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k145_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k145_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k145_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k145_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k145_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TTsaaD 4 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k145_4_6_50 k h.1 (by omega)
theorem s145_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 4 7 = true := by decide +kernel
theorem s145_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 0 = true := by decide +kernel
theorem s145_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 1 = true := by decide +kernel
theorem s145_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 2 = true := by decide +kernel
theorem s145_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 3 = true := by decide +kernel
theorem s145_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 4 = true := by decide +kernel
theorem s145_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 5 = true := by decide +kernel
theorem k145_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k145_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k145_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k145_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k145_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k145_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s145_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k145_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k145_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k145_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k145_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k145_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 145) ((InDA2.TCasaD 5 5 6).getD (145 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k145_5_6_50 k h.1 (by omega)
theorem s145_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 5 7 = true := by decide +kernel
theorem col145_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 6 v) = true := by decide +kernel
theorem col145_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 7 v) = true := by decide +kernel
theorem col145 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 145) 145 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col145_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col145_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s145_2_0
    · exact s145_2_1
    · exact s145_2_2
    · exact s145_2_3
    · exact s145_2_4
    · exact s145_2_5
    · exact s145_2_6
    · exact s145_2_7
  · fin_cases v
    · exact s145_3_0
    · exact s145_3_1
    · exact s145_3_2
    · exact s145_3_3
    · exact s145_3_4
    · exact s145_3_5
    · exact s145_3_6
    · exact s145_3_7
  · fin_cases v
    · exact s145_4_0
    · exact s145_4_1
    · exact s145_4_2
    · exact s145_4_3
    · exact s145_4_4
    · exact s145_4_5
    · exact s145_4_6
    · exact s145_4_7
  · fin_cases v
    · exact s145_5_0
    · exact s145_5_1
    · exact s145_5_2
    · exact s145_5_3
    · exact s145_5_4
    · exact s145_5_5
    · exact s145_5_6
    · exact s145_5_7
  · exact List.all_eq_true.mp col145_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col145_7 v (List.mem_finRange v)
theorem col146_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 0 v) = true := by decide +kernel
theorem col146_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 1 v) = true := by decide +kernel
theorem s146_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 0 = true := by decide +kernel
theorem s146_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 1 = true := by decide +kernel
theorem s146_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 2 = true := by decide +kernel
theorem s146_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 3 = true := by decide +kernel
theorem k146_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k146_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k146_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s146_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k146_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k146_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k146_2_4_80 k h.1 (by omega)
theorem s146_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 5 = true := by decide +kernel
theorem s146_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 6 = true := by decide +kernel
theorem s146_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 2 7 = true := by decide +kernel
theorem s146_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 0 = true := by decide +kernel
theorem s146_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 1 = true := by decide +kernel
theorem s146_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 2 = true := by decide +kernel
theorem s146_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 3 = true := by decide +kernel
theorem k146_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k146_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k146_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s146_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k146_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k146_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k146_3_4_80 k h.1 (by omega)
theorem s146_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 5 = true := by decide +kernel
theorem s146_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 6 = true := by decide +kernel
theorem s146_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 3 7 = true := by decide +kernel
theorem s146_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 0 = true := by decide +kernel
theorem s146_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 1 = true := by decide +kernel
theorem s146_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 2 = true := by decide +kernel
theorem s146_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 3 = true := by decide +kernel
theorem k146_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k146_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k146_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k146_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k146_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k146_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k146_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k146_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k146_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k146_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k146_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k146_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k146_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k146_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k146_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k146_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k146_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k146_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k146_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k146_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k146_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s146_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k146_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k146_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k146_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k146_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k146_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k146_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k146_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k146_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k146_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k146_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k146_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k146_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k146_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k146_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k146_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k146_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k146_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k146_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k146_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k146_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k146_4_4_100 k h.1 (by omega)
theorem k146_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k146_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k146_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k146_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k146_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k146_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k146_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k146_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k146_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s146_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k146_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k146_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k146_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k146_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k146_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k146_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k146_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k146_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 146) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (146 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k146_4_5_40 k h.1 (by omega)
theorem k146_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k146_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k146_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k146_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k146_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k146_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k146_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k146_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k146_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k146_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k146_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s146_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k146_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k146_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k146_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k146_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k146_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k146_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k146_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k146_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k146_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k146_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TTsaaD 4 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k146_4_6_50 k h.1 (by omega)
theorem s146_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 4 7 = true := by decide +kernel
theorem s146_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 0 = true := by decide +kernel
theorem s146_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 1 = true := by decide +kernel
theorem s146_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 2 = true := by decide +kernel
theorem s146_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 3 = true := by decide +kernel
theorem s146_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 4 = true := by decide +kernel
theorem s146_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 5 = true := by decide +kernel
theorem k146_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k146_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k146_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k146_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k146_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k146_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s146_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k146_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k146_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k146_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k146_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k146_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 146) ((InDA2.TCasaD 5 5 6).getD (146 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k146_5_6_50 k h.1 (by omega)
theorem s146_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 5 7 = true := by decide +kernel
theorem col146_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 6 v) = true := by decide +kernel
theorem col146_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 7 v) = true := by decide +kernel
theorem col146 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 146) 146 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col146_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col146_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s146_2_0
    · exact s146_2_1
    · exact s146_2_2
    · exact s146_2_3
    · exact s146_2_4
    · exact s146_2_5
    · exact s146_2_6
    · exact s146_2_7
  · fin_cases v
    · exact s146_3_0
    · exact s146_3_1
    · exact s146_3_2
    · exact s146_3_3
    · exact s146_3_4
    · exact s146_3_5
    · exact s146_3_6
    · exact s146_3_7
  · fin_cases v
    · exact s146_4_0
    · exact s146_4_1
    · exact s146_4_2
    · exact s146_4_3
    · exact s146_4_4
    · exact s146_4_5
    · exact s146_4_6
    · exact s146_4_7
  · fin_cases v
    · exact s146_5_0
    · exact s146_5_1
    · exact s146_5_2
    · exact s146_5_3
    · exact s146_5_4
    · exact s146_5_5
    · exact s146_5_6
    · exact s146_5_7
  · exact List.all_eq_true.mp col146_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col146_7 v (List.mem_finRange v)
theorem col147_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 0 v) = true := by decide +kernel
theorem col147_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 1 v) = true := by decide +kernel
theorem s147_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 0 = true := by decide +kernel
theorem s147_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 1 = true := by decide +kernel
theorem s147_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 2 = true := by decide +kernel
theorem s147_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 3 = true := by decide +kernel
theorem k147_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k147_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k147_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s147_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k147_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k147_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k147_2_4_80 k h.1 (by omega)
theorem s147_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 5 = true := by decide +kernel
theorem s147_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 6 = true := by decide +kernel
theorem s147_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 2 7 = true := by decide +kernel
theorem s147_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 0 = true := by decide +kernel
theorem s147_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 1 = true := by decide +kernel
theorem s147_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 2 = true := by decide +kernel
theorem s147_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 3 = true := by decide +kernel
theorem k147_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k147_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k147_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s147_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k147_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k147_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k147_3_4_80 k h.1 (by omega)
theorem s147_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 5 = true := by decide +kernel
theorem s147_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 6 = true := by decide +kernel
theorem s147_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 3 7 = true := by decide +kernel
theorem s147_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 0 = true := by decide +kernel
theorem s147_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 1 = true := by decide +kernel
theorem s147_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 2 = true := by decide +kernel
theorem s147_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 3 = true := by decide +kernel
theorem k147_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k147_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k147_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k147_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k147_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k147_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k147_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k147_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k147_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k147_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k147_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k147_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k147_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k147_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k147_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k147_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k147_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k147_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k147_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k147_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k147_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s147_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k147_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k147_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k147_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k147_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k147_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k147_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k147_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k147_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k147_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k147_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k147_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k147_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k147_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k147_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k147_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k147_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k147_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k147_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k147_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k147_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k147_4_4_100 k h.1 (by omega)
theorem k147_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k147_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k147_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k147_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k147_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k147_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k147_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k147_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k147_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s147_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k147_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k147_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k147_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k147_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k147_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k147_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k147_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k147_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 147) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (147 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k147_4_5_40 k h.1 (by omega)
theorem k147_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k147_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k147_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k147_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k147_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k147_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k147_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k147_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k147_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k147_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k147_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s147_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k147_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k147_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k147_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k147_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k147_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k147_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k147_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k147_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k147_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k147_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TTsaaD 4 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k147_4_6_50 k h.1 (by omega)
theorem s147_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 4 7 = true := by decide +kernel
theorem s147_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 0 = true := by decide +kernel
theorem s147_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 1 = true := by decide +kernel
theorem s147_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 2 = true := by decide +kernel
theorem s147_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 3 = true := by decide +kernel
theorem s147_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 4 = true := by decide +kernel
theorem s147_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 5 = true := by decide +kernel
theorem k147_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k147_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k147_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k147_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k147_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k147_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s147_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k147_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k147_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k147_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k147_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k147_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 147) ((InDA2.TCasaD 5 5 6).getD (147 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k147_5_6_50 k h.1 (by omega)
theorem s147_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 5 7 = true := by decide +kernel
theorem col147_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 6 v) = true := by decide +kernel
theorem col147_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 7 v) = true := by decide +kernel
theorem col147 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 147) 147 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col147_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col147_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s147_2_0
    · exact s147_2_1
    · exact s147_2_2
    · exact s147_2_3
    · exact s147_2_4
    · exact s147_2_5
    · exact s147_2_6
    · exact s147_2_7
  · fin_cases v
    · exact s147_3_0
    · exact s147_3_1
    · exact s147_3_2
    · exact s147_3_3
    · exact s147_3_4
    · exact s147_3_5
    · exact s147_3_6
    · exact s147_3_7
  · fin_cases v
    · exact s147_4_0
    · exact s147_4_1
    · exact s147_4_2
    · exact s147_4_3
    · exact s147_4_4
    · exact s147_4_5
    · exact s147_4_6
    · exact s147_4_7
  · fin_cases v
    · exact s147_5_0
    · exact s147_5_1
    · exact s147_5_2
    · exact s147_5_3
    · exact s147_5_4
    · exact s147_5_5
    · exact s147_5_6
    · exact s147_5_7
  · exact List.all_eq_true.mp col147_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col147_7 v (List.mem_finRange v)
theorem col148_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 0 v) = true := by decide +kernel
theorem col148_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 1 v) = true := by decide +kernel
theorem s148_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 0 = true := by decide +kernel
theorem s148_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 1 = true := by decide +kernel
theorem s148_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 2 = true := by decide +kernel
theorem s148_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 3 = true := by decide +kernel
theorem k148_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k148_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k148_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s148_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k148_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k148_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k148_2_4_80 k h.1 (by omega)
theorem s148_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 5 = true := by decide +kernel
theorem s148_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 6 = true := by decide +kernel
theorem s148_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 2 7 = true := by decide +kernel
theorem s148_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 0 = true := by decide +kernel
theorem s148_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 1 = true := by decide +kernel
theorem s148_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 2 = true := by decide +kernel
theorem s148_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 3 = true := by decide +kernel
theorem k148_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k148_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k148_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s148_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k148_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k148_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k148_3_4_80 k h.1 (by omega)
theorem s148_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 5 = true := by decide +kernel
theorem s148_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 6 = true := by decide +kernel
theorem s148_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 3 7 = true := by decide +kernel
theorem s148_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 0 = true := by decide +kernel
theorem s148_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 1 = true := by decide +kernel
theorem s148_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 2 = true := by decide +kernel
theorem s148_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 3 = true := by decide +kernel
theorem k148_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k148_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k148_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k148_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k148_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k148_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k148_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k148_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k148_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k148_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k148_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k148_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k148_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k148_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k148_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k148_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k148_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k148_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k148_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k148_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k148_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s148_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k148_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k148_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k148_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k148_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k148_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k148_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k148_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k148_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k148_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k148_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k148_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k148_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k148_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k148_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k148_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k148_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k148_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k148_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k148_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k148_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k148_4_4_100 k h.1 (by omega)
theorem k148_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k148_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k148_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k148_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k148_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k148_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k148_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k148_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k148_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s148_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k148_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k148_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k148_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k148_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k148_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k148_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k148_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k148_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 148) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (148 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k148_4_5_40 k h.1 (by omega)
theorem k148_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k148_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k148_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k148_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k148_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k148_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k148_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k148_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k148_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k148_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k148_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s148_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k148_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k148_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k148_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k148_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k148_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k148_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k148_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k148_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k148_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k148_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TTsaaD 4 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k148_4_6_50 k h.1 (by omega)
theorem s148_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 4 7 = true := by decide +kernel
theorem s148_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 0 = true := by decide +kernel
theorem s148_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 1 = true := by decide +kernel
theorem s148_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 2 = true := by decide +kernel
theorem s148_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 3 = true := by decide +kernel
theorem s148_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 4 = true := by decide +kernel
theorem s148_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 5 = true := by decide +kernel
theorem k148_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k148_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k148_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k148_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k148_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k148_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s148_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k148_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k148_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k148_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k148_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k148_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 148) ((InDA2.TCasaD 5 5 6).getD (148 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k148_5_6_50 k h.1 (by omega)
theorem s148_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 5 7 = true := by decide +kernel
theorem col148_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 6 v) = true := by decide +kernel
theorem col148_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 7 v) = true := by decide +kernel
theorem col148 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 148) 148 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col148_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col148_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s148_2_0
    · exact s148_2_1
    · exact s148_2_2
    · exact s148_2_3
    · exact s148_2_4
    · exact s148_2_5
    · exact s148_2_6
    · exact s148_2_7
  · fin_cases v
    · exact s148_3_0
    · exact s148_3_1
    · exact s148_3_2
    · exact s148_3_3
    · exact s148_3_4
    · exact s148_3_5
    · exact s148_3_6
    · exact s148_3_7
  · fin_cases v
    · exact s148_4_0
    · exact s148_4_1
    · exact s148_4_2
    · exact s148_4_3
    · exact s148_4_4
    · exact s148_4_5
    · exact s148_4_6
    · exact s148_4_7
  · fin_cases v
    · exact s148_5_0
    · exact s148_5_1
    · exact s148_5_2
    · exact s148_5_3
    · exact s148_5_4
    · exact s148_5_5
    · exact s148_5_6
    · exact s148_5_7
  · exact List.all_eq_true.mp col148_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col148_7 v (List.mem_finRange v)
theorem col149_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 0 v) = true := by decide +kernel
theorem col149_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 1 v) = true := by decide +kernel
theorem s149_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 0 = true := by decide +kernel
theorem s149_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 1 = true := by decide +kernel
theorem s149_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 2 = true := by decide +kernel
theorem s149_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 3 = true := by decide +kernel
theorem k149_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k149_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k149_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s149_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k149_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k149_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k149_2_4_80 k h.1 (by omega)
theorem s149_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 5 = true := by decide +kernel
theorem s149_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 6 = true := by decide +kernel
theorem s149_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 2 7 = true := by decide +kernel
theorem s149_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 0 = true := by decide +kernel
theorem s149_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 1 = true := by decide +kernel
theorem s149_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 2 = true := by decide +kernel
theorem s149_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 3 = true := by decide +kernel
theorem k149_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k149_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k149_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s149_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k149_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k149_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k149_3_4_80 k h.1 (by omega)
theorem s149_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 5 = true := by decide +kernel
theorem s149_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 6 = true := by decide +kernel
theorem s149_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 3 7 = true := by decide +kernel
theorem s149_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 0 = true := by decide +kernel
theorem s149_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 1 = true := by decide +kernel
theorem s149_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 2 = true := by decide +kernel
theorem s149_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 3 = true := by decide +kernel
theorem k149_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k149_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k149_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k149_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k149_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k149_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k149_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k149_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k149_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k149_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k149_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k149_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k149_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k149_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k149_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k149_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k149_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k149_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k149_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k149_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k149_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s149_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k149_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k149_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k149_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k149_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k149_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k149_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k149_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k149_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k149_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k149_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k149_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k149_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k149_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k149_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k149_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k149_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k149_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k149_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k149_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k149_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k149_4_4_100 k h.1 (by omega)
theorem k149_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k149_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k149_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k149_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k149_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k149_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k149_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k149_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k149_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s149_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k149_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k149_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k149_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k149_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k149_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k149_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k149_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k149_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 149) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (149 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k149_4_5_40 k h.1 (by omega)
theorem k149_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k149_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k149_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k149_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k149_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k149_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k149_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k149_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k149_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k149_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k149_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s149_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k149_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k149_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k149_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k149_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k149_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k149_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k149_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k149_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k149_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k149_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TTsaaD 4 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k149_4_6_50 k h.1 (by omega)
theorem s149_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 4 7 = true := by decide +kernel
theorem s149_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 0 = true := by decide +kernel
theorem s149_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 1 = true := by decide +kernel
theorem s149_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 2 = true := by decide +kernel
theorem s149_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 3 = true := by decide +kernel
theorem s149_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 4 = true := by decide +kernel
theorem s149_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 5 = true := by decide +kernel
theorem k149_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k149_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k149_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k149_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k149_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k149_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s149_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k149_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k149_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k149_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k149_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k149_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 149) ((InDA2.TCasaD 5 5 6).getD (149 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k149_5_6_50 k h.1 (by omega)
theorem s149_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 5 7 = true := by decide +kernel
theorem col149_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 6 v) = true := by decide +kernel
theorem col149_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 7 v) = true := by decide +kernel
theorem col149 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 149) 149 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col149_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col149_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s149_2_0
    · exact s149_2_1
    · exact s149_2_2
    · exact s149_2_3
    · exact s149_2_4
    · exact s149_2_5
    · exact s149_2_6
    · exact s149_2_7
  · fin_cases v
    · exact s149_3_0
    · exact s149_3_1
    · exact s149_3_2
    · exact s149_3_3
    · exact s149_3_4
    · exact s149_3_5
    · exact s149_3_6
    · exact s149_3_7
  · fin_cases v
    · exact s149_4_0
    · exact s149_4_1
    · exact s149_4_2
    · exact s149_4_3
    · exact s149_4_4
    · exact s149_4_5
    · exact s149_4_6
    · exact s149_4_7
  · fin_cases v
    · exact s149_5_0
    · exact s149_5_1
    · exact s149_5_2
    · exact s149_5_3
    · exact s149_5_4
    · exact s149_5_5
    · exact s149_5_6
    · exact s149_5_7
  · exact List.all_eq_true.mp col149_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col149_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
