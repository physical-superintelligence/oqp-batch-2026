module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [165, 170). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col165_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 0 v) = true := by decide +kernel
theorem col165_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 1 v) = true := by decide +kernel
theorem s165_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 0 = true := by decide +kernel
theorem s165_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 1 = true := by decide +kernel
theorem s165_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 2 = true := by decide +kernel
theorem s165_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 3 = true := by decide +kernel
theorem k165_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k165_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k165_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s165_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k165_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k165_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k165_2_4_80 k h.1 (by omega)
theorem s165_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 5 = true := by decide +kernel
theorem s165_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 6 = true := by decide +kernel
theorem s165_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 2 7 = true := by decide +kernel
theorem s165_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 0 = true := by decide +kernel
theorem s165_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 1 = true := by decide +kernel
theorem s165_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 2 = true := by decide +kernel
theorem s165_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 3 = true := by decide +kernel
theorem k165_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k165_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k165_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s165_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k165_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k165_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k165_3_4_80 k h.1 (by omega)
theorem s165_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 5 = true := by decide +kernel
theorem s165_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 6 = true := by decide +kernel
theorem s165_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 3 7 = true := by decide +kernel
theorem s165_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 0 = true := by decide +kernel
theorem s165_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 1 = true := by decide +kernel
theorem s165_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 2 = true := by decide +kernel
theorem s165_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 3 = true := by decide +kernel
theorem k165_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k165_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k165_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k165_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k165_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k165_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k165_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k165_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k165_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k165_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k165_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k165_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k165_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k165_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k165_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k165_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k165_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k165_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k165_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k165_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k165_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s165_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k165_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k165_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k165_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k165_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k165_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k165_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k165_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k165_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k165_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k165_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k165_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k165_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k165_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k165_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k165_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k165_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k165_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k165_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k165_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k165_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k165_4_4_100 k h.1 (by omega)
theorem k165_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k165_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k165_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k165_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k165_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k165_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k165_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k165_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k165_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s165_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k165_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k165_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k165_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k165_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k165_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k165_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k165_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k165_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 165) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (165 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k165_4_5_40 k h.1 (by omega)
theorem k165_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k165_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k165_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k165_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k165_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k165_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k165_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k165_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k165_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k165_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k165_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s165_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k165_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k165_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k165_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k165_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k165_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k165_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k165_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k165_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k165_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k165_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TTsaaD 4 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k165_4_6_50 k h.1 (by omega)
theorem s165_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 4 7 = true := by decide +kernel
theorem s165_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 0 = true := by decide +kernel
theorem s165_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 1 = true := by decide +kernel
theorem s165_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 2 = true := by decide +kernel
theorem s165_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 3 = true := by decide +kernel
theorem s165_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 4 = true := by decide +kernel
theorem s165_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 5 = true := by decide +kernel
theorem k165_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k165_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k165_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k165_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k165_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k165_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s165_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k165_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k165_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k165_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k165_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k165_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 165) ((InDA2.TCasaD 5 5 6).getD (165 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k165_5_6_50 k h.1 (by omega)
theorem s165_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 5 7 = true := by decide +kernel
theorem col165_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 6 v) = true := by decide +kernel
theorem col165_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 7 v) = true := by decide +kernel
theorem col165 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 165) 165 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col165_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col165_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s165_2_0
    · exact s165_2_1
    · exact s165_2_2
    · exact s165_2_3
    · exact s165_2_4
    · exact s165_2_5
    · exact s165_2_6
    · exact s165_2_7
  · fin_cases v
    · exact s165_3_0
    · exact s165_3_1
    · exact s165_3_2
    · exact s165_3_3
    · exact s165_3_4
    · exact s165_3_5
    · exact s165_3_6
    · exact s165_3_7
  · fin_cases v
    · exact s165_4_0
    · exact s165_4_1
    · exact s165_4_2
    · exact s165_4_3
    · exact s165_4_4
    · exact s165_4_5
    · exact s165_4_6
    · exact s165_4_7
  · fin_cases v
    · exact s165_5_0
    · exact s165_5_1
    · exact s165_5_2
    · exact s165_5_3
    · exact s165_5_4
    · exact s165_5_5
    · exact s165_5_6
    · exact s165_5_7
  · exact List.all_eq_true.mp col165_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col165_7 v (List.mem_finRange v)
theorem col166_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 0 v) = true := by decide +kernel
theorem col166_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 1 v) = true := by decide +kernel
theorem s166_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 0 = true := by decide +kernel
theorem s166_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 1 = true := by decide +kernel
theorem s166_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 2 = true := by decide +kernel
theorem s166_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 3 = true := by decide +kernel
theorem k166_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k166_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k166_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s166_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k166_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k166_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k166_2_4_80 k h.1 (by omega)
theorem s166_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 5 = true := by decide +kernel
theorem s166_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 6 = true := by decide +kernel
theorem s166_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 2 7 = true := by decide +kernel
theorem s166_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 0 = true := by decide +kernel
theorem s166_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 1 = true := by decide +kernel
theorem s166_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 2 = true := by decide +kernel
theorem s166_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 3 = true := by decide +kernel
theorem k166_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k166_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k166_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s166_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k166_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k166_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k166_3_4_80 k h.1 (by omega)
theorem s166_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 5 = true := by decide +kernel
theorem s166_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 6 = true := by decide +kernel
theorem s166_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 3 7 = true := by decide +kernel
theorem s166_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 0 = true := by decide +kernel
theorem s166_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 1 = true := by decide +kernel
theorem s166_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 2 = true := by decide +kernel
theorem s166_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 3 = true := by decide +kernel
theorem k166_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k166_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k166_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k166_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k166_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k166_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k166_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k166_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k166_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k166_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k166_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k166_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k166_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k166_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k166_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k166_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k166_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k166_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k166_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k166_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k166_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s166_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k166_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k166_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k166_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k166_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k166_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k166_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k166_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k166_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k166_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k166_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k166_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k166_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k166_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k166_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k166_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k166_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k166_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k166_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k166_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k166_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k166_4_4_100 k h.1 (by omega)
theorem k166_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k166_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k166_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k166_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k166_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k166_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k166_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k166_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k166_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s166_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k166_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k166_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k166_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k166_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k166_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k166_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k166_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k166_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 166) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (166 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k166_4_5_40 k h.1 (by omega)
theorem k166_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k166_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k166_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k166_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k166_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k166_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k166_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k166_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k166_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k166_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k166_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s166_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k166_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k166_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k166_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k166_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k166_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k166_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k166_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k166_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k166_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k166_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TTsaaD 4 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k166_4_6_50 k h.1 (by omega)
theorem s166_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 4 7 = true := by decide +kernel
theorem s166_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 0 = true := by decide +kernel
theorem s166_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 1 = true := by decide +kernel
theorem s166_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 2 = true := by decide +kernel
theorem s166_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 3 = true := by decide +kernel
theorem s166_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 4 = true := by decide +kernel
theorem s166_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 5 = true := by decide +kernel
theorem k166_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k166_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k166_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k166_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k166_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k166_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s166_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k166_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k166_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k166_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k166_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k166_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 166) ((InDA2.TCasaD 5 5 6).getD (166 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k166_5_6_50 k h.1 (by omega)
theorem s166_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 5 7 = true := by decide +kernel
theorem col166_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 6 v) = true := by decide +kernel
theorem col166_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 7 v) = true := by decide +kernel
theorem col166 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 166) 166 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col166_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col166_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s166_2_0
    · exact s166_2_1
    · exact s166_2_2
    · exact s166_2_3
    · exact s166_2_4
    · exact s166_2_5
    · exact s166_2_6
    · exact s166_2_7
  · fin_cases v
    · exact s166_3_0
    · exact s166_3_1
    · exact s166_3_2
    · exact s166_3_3
    · exact s166_3_4
    · exact s166_3_5
    · exact s166_3_6
    · exact s166_3_7
  · fin_cases v
    · exact s166_4_0
    · exact s166_4_1
    · exact s166_4_2
    · exact s166_4_3
    · exact s166_4_4
    · exact s166_4_5
    · exact s166_4_6
    · exact s166_4_7
  · fin_cases v
    · exact s166_5_0
    · exact s166_5_1
    · exact s166_5_2
    · exact s166_5_3
    · exact s166_5_4
    · exact s166_5_5
    · exact s166_5_6
    · exact s166_5_7
  · exact List.all_eq_true.mp col166_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col166_7 v (List.mem_finRange v)
theorem col167_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 0 v) = true := by decide +kernel
theorem col167_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 1 v) = true := by decide +kernel
theorem s167_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 0 = true := by decide +kernel
theorem s167_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 1 = true := by decide +kernel
theorem s167_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 2 = true := by decide +kernel
theorem s167_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 3 = true := by decide +kernel
theorem k167_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k167_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k167_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s167_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k167_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k167_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k167_2_4_80 k h.1 (by omega)
theorem s167_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 5 = true := by decide +kernel
theorem s167_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 6 = true := by decide +kernel
theorem s167_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 2 7 = true := by decide +kernel
theorem s167_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 0 = true := by decide +kernel
theorem s167_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 1 = true := by decide +kernel
theorem s167_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 2 = true := by decide +kernel
theorem s167_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 3 = true := by decide +kernel
theorem k167_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k167_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k167_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s167_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k167_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k167_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k167_3_4_80 k h.1 (by omega)
theorem s167_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 5 = true := by decide +kernel
theorem s167_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 6 = true := by decide +kernel
theorem s167_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 3 7 = true := by decide +kernel
theorem s167_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 0 = true := by decide +kernel
theorem s167_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 1 = true := by decide +kernel
theorem s167_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 2 = true := by decide +kernel
theorem s167_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 3 = true := by decide +kernel
theorem k167_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k167_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k167_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k167_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k167_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k167_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k167_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k167_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k167_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k167_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k167_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k167_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k167_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k167_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k167_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k167_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k167_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k167_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k167_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k167_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k167_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s167_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k167_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k167_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k167_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k167_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k167_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k167_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k167_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k167_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k167_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k167_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k167_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k167_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k167_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k167_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k167_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k167_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k167_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k167_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k167_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k167_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k167_4_4_100 k h.1 (by omega)
theorem k167_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k167_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k167_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k167_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k167_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k167_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k167_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k167_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k167_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s167_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k167_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k167_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k167_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k167_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k167_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k167_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k167_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k167_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 167) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (167 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k167_4_5_40 k h.1 (by omega)
theorem k167_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k167_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k167_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k167_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k167_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k167_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k167_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k167_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k167_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k167_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k167_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s167_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k167_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k167_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k167_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k167_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k167_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k167_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k167_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k167_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k167_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k167_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TTsaaD 4 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k167_4_6_50 k h.1 (by omega)
theorem s167_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 4 7 = true := by decide +kernel
theorem s167_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 0 = true := by decide +kernel
theorem s167_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 1 = true := by decide +kernel
theorem s167_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 2 = true := by decide +kernel
theorem s167_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 3 = true := by decide +kernel
theorem s167_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 4 = true := by decide +kernel
theorem s167_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 5 = true := by decide +kernel
theorem k167_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k167_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k167_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k167_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k167_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k167_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s167_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k167_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k167_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k167_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k167_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k167_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 167) ((InDA2.TCasaD 5 5 6).getD (167 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k167_5_6_50 k h.1 (by omega)
theorem s167_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 5 7 = true := by decide +kernel
theorem col167_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 6 v) = true := by decide +kernel
theorem col167_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 7 v) = true := by decide +kernel
theorem col167 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 167) 167 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col167_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col167_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s167_2_0
    · exact s167_2_1
    · exact s167_2_2
    · exact s167_2_3
    · exact s167_2_4
    · exact s167_2_5
    · exact s167_2_6
    · exact s167_2_7
  · fin_cases v
    · exact s167_3_0
    · exact s167_3_1
    · exact s167_3_2
    · exact s167_3_3
    · exact s167_3_4
    · exact s167_3_5
    · exact s167_3_6
    · exact s167_3_7
  · fin_cases v
    · exact s167_4_0
    · exact s167_4_1
    · exact s167_4_2
    · exact s167_4_3
    · exact s167_4_4
    · exact s167_4_5
    · exact s167_4_6
    · exact s167_4_7
  · fin_cases v
    · exact s167_5_0
    · exact s167_5_1
    · exact s167_5_2
    · exact s167_5_3
    · exact s167_5_4
    · exact s167_5_5
    · exact s167_5_6
    · exact s167_5_7
  · exact List.all_eq_true.mp col167_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col167_7 v (List.mem_finRange v)
theorem col168_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 0 v) = true := by decide +kernel
theorem col168_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 1 v) = true := by decide +kernel
theorem s168_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 0 = true := by decide +kernel
theorem s168_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 1 = true := by decide +kernel
theorem s168_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 2 = true := by decide +kernel
theorem s168_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 3 = true := by decide +kernel
theorem k168_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k168_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k168_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s168_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k168_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k168_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k168_2_4_80 k h.1 (by omega)
theorem s168_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 5 = true := by decide +kernel
theorem s168_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 6 = true := by decide +kernel
theorem s168_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 2 7 = true := by decide +kernel
theorem s168_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 0 = true := by decide +kernel
theorem s168_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 1 = true := by decide +kernel
theorem s168_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 2 = true := by decide +kernel
theorem s168_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 3 = true := by decide +kernel
theorem k168_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k168_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k168_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s168_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k168_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k168_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k168_3_4_80 k h.1 (by omega)
theorem s168_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 5 = true := by decide +kernel
theorem s168_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 6 = true := by decide +kernel
theorem s168_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 3 7 = true := by decide +kernel
theorem s168_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 0 = true := by decide +kernel
theorem s168_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 1 = true := by decide +kernel
theorem s168_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 2 = true := by decide +kernel
theorem s168_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 3 = true := by decide +kernel
theorem k168_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k168_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k168_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k168_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k168_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k168_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k168_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k168_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k168_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k168_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k168_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k168_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k168_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k168_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k168_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k168_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k168_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k168_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k168_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k168_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k168_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s168_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k168_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k168_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k168_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k168_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k168_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k168_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k168_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k168_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k168_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k168_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k168_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k168_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k168_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k168_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k168_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k168_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k168_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k168_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k168_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k168_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k168_4_4_100 k h.1 (by omega)
theorem k168_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k168_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k168_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k168_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k168_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k168_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k168_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k168_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k168_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s168_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k168_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k168_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k168_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k168_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k168_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k168_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k168_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k168_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 168) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (168 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k168_4_5_40 k h.1 (by omega)
theorem k168_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k168_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k168_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k168_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k168_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k168_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k168_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k168_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k168_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k168_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k168_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s168_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k168_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k168_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k168_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k168_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k168_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k168_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k168_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k168_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k168_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k168_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TTsaaD 4 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k168_4_6_50 k h.1 (by omega)
theorem s168_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 4 7 = true := by decide +kernel
theorem s168_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 0 = true := by decide +kernel
theorem s168_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 1 = true := by decide +kernel
theorem s168_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 2 = true := by decide +kernel
theorem s168_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 3 = true := by decide +kernel
theorem s168_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 4 = true := by decide +kernel
theorem s168_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 5 = true := by decide +kernel
theorem k168_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k168_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k168_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k168_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k168_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k168_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s168_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k168_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k168_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k168_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k168_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k168_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 168) ((InDA2.TCasaD 5 5 6).getD (168 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k168_5_6_50 k h.1 (by omega)
theorem s168_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 5 7 = true := by decide +kernel
theorem col168_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 6 v) = true := by decide +kernel
theorem col168_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 7 v) = true := by decide +kernel
theorem col168 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 168) 168 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col168_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col168_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s168_2_0
    · exact s168_2_1
    · exact s168_2_2
    · exact s168_2_3
    · exact s168_2_4
    · exact s168_2_5
    · exact s168_2_6
    · exact s168_2_7
  · fin_cases v
    · exact s168_3_0
    · exact s168_3_1
    · exact s168_3_2
    · exact s168_3_3
    · exact s168_3_4
    · exact s168_3_5
    · exact s168_3_6
    · exact s168_3_7
  · fin_cases v
    · exact s168_4_0
    · exact s168_4_1
    · exact s168_4_2
    · exact s168_4_3
    · exact s168_4_4
    · exact s168_4_5
    · exact s168_4_6
    · exact s168_4_7
  · fin_cases v
    · exact s168_5_0
    · exact s168_5_1
    · exact s168_5_2
    · exact s168_5_3
    · exact s168_5_4
    · exact s168_5_5
    · exact s168_5_6
    · exact s168_5_7
  · exact List.all_eq_true.mp col168_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col168_7 v (List.mem_finRange v)
theorem col169_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 0 v) = true := by decide +kernel
theorem col169_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 1 v) = true := by decide +kernel
theorem s169_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 0 = true := by decide +kernel
theorem s169_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 1 = true := by decide +kernel
theorem s169_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 2 = true := by decide +kernel
theorem s169_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 3 = true := by decide +kernel
theorem k169_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k169_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k169_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s169_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k169_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k169_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k169_2_4_80 k h.1 (by omega)
theorem s169_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 5 = true := by decide +kernel
theorem s169_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 6 = true := by decide +kernel
theorem s169_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 2 7 = true := by decide +kernel
theorem s169_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 0 = true := by decide +kernel
theorem s169_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 1 = true := by decide +kernel
theorem s169_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 2 = true := by decide +kernel
theorem s169_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 3 = true := by decide +kernel
theorem k169_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k169_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k169_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s169_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k169_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k169_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k169_3_4_80 k h.1 (by omega)
theorem s169_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 5 = true := by decide +kernel
theorem s169_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 6 = true := by decide +kernel
theorem s169_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 3 7 = true := by decide +kernel
theorem s169_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 0 = true := by decide +kernel
theorem s169_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 1 = true := by decide +kernel
theorem s169_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 2 = true := by decide +kernel
theorem s169_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 3 = true := by decide +kernel
theorem k169_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k169_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k169_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k169_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k169_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k169_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k169_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k169_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k169_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k169_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k169_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k169_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k169_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k169_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k169_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k169_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k169_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k169_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k169_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k169_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k169_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s169_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k169_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k169_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k169_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k169_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k169_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k169_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k169_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k169_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k169_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k169_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k169_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k169_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k169_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k169_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k169_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k169_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k169_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k169_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k169_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k169_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k169_4_4_100 k h.1 (by omega)
theorem k169_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k169_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k169_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k169_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k169_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k169_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k169_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k169_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k169_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s169_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k169_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k169_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k169_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k169_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k169_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k169_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k169_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k169_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 169) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (169 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k169_4_5_40 k h.1 (by omega)
theorem k169_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k169_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k169_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k169_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k169_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k169_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k169_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k169_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k169_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k169_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k169_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s169_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k169_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k169_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k169_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k169_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k169_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k169_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k169_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k169_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k169_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k169_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TTsaaD 4 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k169_4_6_50 k h.1 (by omega)
theorem s169_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 4 7 = true := by decide +kernel
theorem s169_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 0 = true := by decide +kernel
theorem s169_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 1 = true := by decide +kernel
theorem s169_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 2 = true := by decide +kernel
theorem s169_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 3 = true := by decide +kernel
theorem s169_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 4 = true := by decide +kernel
theorem s169_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 5 = true := by decide +kernel
theorem k169_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k169_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k169_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k169_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k169_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k169_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s169_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k169_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k169_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k169_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k169_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k169_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 169) ((InDA2.TCasaD 5 5 6).getD (169 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k169_5_6_50 k h.1 (by omega)
theorem s169_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 5 7 = true := by decide +kernel
theorem col169_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 6 v) = true := by decide +kernel
theorem col169_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 7 v) = true := by decide +kernel
theorem col169 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 169) 169 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col169_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col169_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s169_2_0
    · exact s169_2_1
    · exact s169_2_2
    · exact s169_2_3
    · exact s169_2_4
    · exact s169_2_5
    · exact s169_2_6
    · exact s169_2_7
  · fin_cases v
    · exact s169_3_0
    · exact s169_3_1
    · exact s169_3_2
    · exact s169_3_3
    · exact s169_3_4
    · exact s169_3_5
    · exact s169_3_6
    · exact s169_3_7
  · fin_cases v
    · exact s169_4_0
    · exact s169_4_1
    · exact s169_4_2
    · exact s169_4_3
    · exact s169_4_4
    · exact s169_4_5
    · exact s169_4_6
    · exact s169_4_7
  · fin_cases v
    · exact s169_5_0
    · exact s169_5_1
    · exact s169_5_2
    · exact s169_5_3
    · exact s169_5_4
    · exact s169_5_5
    · exact s169_5_6
    · exact s169_5_7
  · exact List.all_eq_true.mp col169_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col169_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
