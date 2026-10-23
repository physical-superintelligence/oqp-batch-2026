module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [155, 160). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col155_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 0 v) = true := by decide +kernel
theorem col155_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 1 v) = true := by decide +kernel
theorem s155_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 0 = true := by decide +kernel
theorem s155_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 1 = true := by decide +kernel
theorem s155_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 2 = true := by decide +kernel
theorem s155_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 3 = true := by decide +kernel
theorem k155_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k155_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k155_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s155_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k155_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k155_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k155_2_4_80 k h.1 (by omega)
theorem s155_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 5 = true := by decide +kernel
theorem s155_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 6 = true := by decide +kernel
theorem s155_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 2 7 = true := by decide +kernel
theorem s155_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 0 = true := by decide +kernel
theorem s155_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 1 = true := by decide +kernel
theorem s155_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 2 = true := by decide +kernel
theorem s155_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 3 = true := by decide +kernel
theorem k155_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k155_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k155_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s155_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k155_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k155_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k155_3_4_80 k h.1 (by omega)
theorem s155_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 5 = true := by decide +kernel
theorem s155_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 6 = true := by decide +kernel
theorem s155_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 3 7 = true := by decide +kernel
theorem s155_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 0 = true := by decide +kernel
theorem s155_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 1 = true := by decide +kernel
theorem s155_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 2 = true := by decide +kernel
theorem s155_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 3 = true := by decide +kernel
theorem k155_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k155_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k155_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k155_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k155_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k155_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k155_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k155_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k155_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k155_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k155_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k155_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k155_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k155_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k155_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k155_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k155_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k155_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k155_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k155_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k155_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s155_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k155_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k155_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k155_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k155_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k155_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k155_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k155_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k155_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k155_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k155_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k155_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k155_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k155_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k155_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k155_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k155_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k155_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k155_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k155_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k155_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k155_4_4_100 k h.1 (by omega)
theorem k155_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k155_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k155_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k155_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k155_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k155_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k155_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k155_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k155_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s155_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k155_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k155_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k155_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k155_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k155_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k155_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k155_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k155_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 155) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (155 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k155_4_5_40 k h.1 (by omega)
theorem k155_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k155_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k155_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k155_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k155_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k155_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k155_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k155_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k155_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k155_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k155_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s155_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k155_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k155_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k155_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k155_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k155_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k155_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k155_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k155_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k155_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k155_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TTsaaD 4 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k155_4_6_50 k h.1 (by omega)
theorem s155_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 4 7 = true := by decide +kernel
theorem s155_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 0 = true := by decide +kernel
theorem s155_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 1 = true := by decide +kernel
theorem s155_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 2 = true := by decide +kernel
theorem s155_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 3 = true := by decide +kernel
theorem s155_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 4 = true := by decide +kernel
theorem s155_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 5 = true := by decide +kernel
theorem k155_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k155_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k155_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k155_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k155_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k155_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s155_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k155_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k155_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k155_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k155_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k155_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 155) ((InDA2.TCasaD 5 5 6).getD (155 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k155_5_6_50 k h.1 (by omega)
theorem s155_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 5 7 = true := by decide +kernel
theorem col155_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 6 v) = true := by decide +kernel
theorem col155_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 7 v) = true := by decide +kernel
theorem col155 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 155) 155 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col155_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col155_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s155_2_0
    · exact s155_2_1
    · exact s155_2_2
    · exact s155_2_3
    · exact s155_2_4
    · exact s155_2_5
    · exact s155_2_6
    · exact s155_2_7
  · fin_cases v
    · exact s155_3_0
    · exact s155_3_1
    · exact s155_3_2
    · exact s155_3_3
    · exact s155_3_4
    · exact s155_3_5
    · exact s155_3_6
    · exact s155_3_7
  · fin_cases v
    · exact s155_4_0
    · exact s155_4_1
    · exact s155_4_2
    · exact s155_4_3
    · exact s155_4_4
    · exact s155_4_5
    · exact s155_4_6
    · exact s155_4_7
  · fin_cases v
    · exact s155_5_0
    · exact s155_5_1
    · exact s155_5_2
    · exact s155_5_3
    · exact s155_5_4
    · exact s155_5_5
    · exact s155_5_6
    · exact s155_5_7
  · exact List.all_eq_true.mp col155_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col155_7 v (List.mem_finRange v)
theorem col156_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 0 v) = true := by decide +kernel
theorem col156_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 1 v) = true := by decide +kernel
theorem s156_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 0 = true := by decide +kernel
theorem s156_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 1 = true := by decide +kernel
theorem s156_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 2 = true := by decide +kernel
theorem s156_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 3 = true := by decide +kernel
theorem k156_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k156_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k156_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s156_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k156_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k156_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k156_2_4_80 k h.1 (by omega)
theorem s156_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 5 = true := by decide +kernel
theorem s156_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 6 = true := by decide +kernel
theorem s156_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 2 7 = true := by decide +kernel
theorem s156_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 0 = true := by decide +kernel
theorem s156_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 1 = true := by decide +kernel
theorem s156_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 2 = true := by decide +kernel
theorem s156_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 3 = true := by decide +kernel
theorem k156_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k156_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k156_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s156_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k156_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k156_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k156_3_4_80 k h.1 (by omega)
theorem s156_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 5 = true := by decide +kernel
theorem s156_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 6 = true := by decide +kernel
theorem s156_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 3 7 = true := by decide +kernel
theorem s156_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 0 = true := by decide +kernel
theorem s156_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 1 = true := by decide +kernel
theorem s156_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 2 = true := by decide +kernel
theorem s156_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 3 = true := by decide +kernel
theorem k156_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k156_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k156_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k156_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k156_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k156_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k156_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k156_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k156_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k156_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k156_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k156_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k156_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k156_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k156_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k156_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k156_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k156_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k156_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k156_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k156_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s156_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k156_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k156_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k156_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k156_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k156_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k156_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k156_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k156_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k156_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k156_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k156_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k156_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k156_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k156_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k156_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k156_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k156_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k156_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k156_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k156_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k156_4_4_100 k h.1 (by omega)
theorem k156_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k156_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k156_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k156_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k156_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k156_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k156_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k156_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k156_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s156_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k156_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k156_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k156_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k156_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k156_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k156_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k156_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k156_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 156) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (156 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k156_4_5_40 k h.1 (by omega)
theorem k156_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k156_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k156_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k156_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k156_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k156_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k156_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k156_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k156_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k156_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k156_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s156_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k156_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k156_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k156_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k156_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k156_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k156_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k156_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k156_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k156_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k156_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TTsaaD 4 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k156_4_6_50 k h.1 (by omega)
theorem s156_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 4 7 = true := by decide +kernel
theorem s156_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 0 = true := by decide +kernel
theorem s156_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 1 = true := by decide +kernel
theorem s156_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 2 = true := by decide +kernel
theorem s156_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 3 = true := by decide +kernel
theorem s156_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 4 = true := by decide +kernel
theorem s156_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 5 = true := by decide +kernel
theorem k156_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k156_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k156_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k156_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k156_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k156_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s156_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k156_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k156_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k156_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k156_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k156_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 156) ((InDA2.TCasaD 5 5 6).getD (156 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k156_5_6_50 k h.1 (by omega)
theorem s156_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 5 7 = true := by decide +kernel
theorem col156_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 6 v) = true := by decide +kernel
theorem col156_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 7 v) = true := by decide +kernel
theorem col156 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 156) 156 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col156_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col156_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s156_2_0
    · exact s156_2_1
    · exact s156_2_2
    · exact s156_2_3
    · exact s156_2_4
    · exact s156_2_5
    · exact s156_2_6
    · exact s156_2_7
  · fin_cases v
    · exact s156_3_0
    · exact s156_3_1
    · exact s156_3_2
    · exact s156_3_3
    · exact s156_3_4
    · exact s156_3_5
    · exact s156_3_6
    · exact s156_3_7
  · fin_cases v
    · exact s156_4_0
    · exact s156_4_1
    · exact s156_4_2
    · exact s156_4_3
    · exact s156_4_4
    · exact s156_4_5
    · exact s156_4_6
    · exact s156_4_7
  · fin_cases v
    · exact s156_5_0
    · exact s156_5_1
    · exact s156_5_2
    · exact s156_5_3
    · exact s156_5_4
    · exact s156_5_5
    · exact s156_5_6
    · exact s156_5_7
  · exact List.all_eq_true.mp col156_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col156_7 v (List.mem_finRange v)
theorem col157_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 0 v) = true := by decide +kernel
theorem col157_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 1 v) = true := by decide +kernel
theorem s157_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 0 = true := by decide +kernel
theorem s157_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 1 = true := by decide +kernel
theorem s157_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 2 = true := by decide +kernel
theorem s157_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 3 = true := by decide +kernel
theorem k157_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k157_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k157_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s157_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k157_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k157_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k157_2_4_80 k h.1 (by omega)
theorem s157_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 5 = true := by decide +kernel
theorem s157_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 6 = true := by decide +kernel
theorem s157_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 2 7 = true := by decide +kernel
theorem s157_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 0 = true := by decide +kernel
theorem s157_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 1 = true := by decide +kernel
theorem s157_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 2 = true := by decide +kernel
theorem s157_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 3 = true := by decide +kernel
theorem k157_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k157_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k157_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s157_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k157_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k157_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k157_3_4_80 k h.1 (by omega)
theorem s157_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 5 = true := by decide +kernel
theorem s157_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 6 = true := by decide +kernel
theorem s157_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 3 7 = true := by decide +kernel
theorem s157_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 0 = true := by decide +kernel
theorem s157_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 1 = true := by decide +kernel
theorem s157_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 2 = true := by decide +kernel
theorem s157_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 3 = true := by decide +kernel
theorem k157_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k157_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k157_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k157_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k157_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k157_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k157_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k157_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k157_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k157_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k157_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k157_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k157_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k157_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k157_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k157_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k157_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k157_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k157_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k157_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k157_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s157_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k157_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k157_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k157_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k157_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k157_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k157_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k157_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k157_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k157_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k157_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k157_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k157_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k157_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k157_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k157_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k157_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k157_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k157_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k157_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k157_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k157_4_4_100 k h.1 (by omega)
theorem k157_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k157_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k157_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k157_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k157_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k157_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k157_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k157_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k157_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s157_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k157_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k157_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k157_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k157_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k157_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k157_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k157_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k157_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 157) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (157 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k157_4_5_40 k h.1 (by omega)
theorem k157_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k157_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k157_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k157_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k157_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k157_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k157_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k157_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k157_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k157_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k157_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s157_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k157_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k157_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k157_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k157_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k157_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k157_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k157_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k157_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k157_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k157_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TTsaaD 4 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k157_4_6_50 k h.1 (by omega)
theorem s157_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 4 7 = true := by decide +kernel
theorem s157_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 0 = true := by decide +kernel
theorem s157_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 1 = true := by decide +kernel
theorem s157_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 2 = true := by decide +kernel
theorem s157_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 3 = true := by decide +kernel
theorem s157_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 4 = true := by decide +kernel
theorem s157_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 5 = true := by decide +kernel
theorem k157_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k157_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k157_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k157_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k157_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k157_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s157_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k157_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k157_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k157_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k157_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k157_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 157) ((InDA2.TCasaD 5 5 6).getD (157 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k157_5_6_50 k h.1 (by omega)
theorem s157_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 5 7 = true := by decide +kernel
theorem col157_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 6 v) = true := by decide +kernel
theorem col157_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 7 v) = true := by decide +kernel
theorem col157 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 157) 157 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col157_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col157_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s157_2_0
    · exact s157_2_1
    · exact s157_2_2
    · exact s157_2_3
    · exact s157_2_4
    · exact s157_2_5
    · exact s157_2_6
    · exact s157_2_7
  · fin_cases v
    · exact s157_3_0
    · exact s157_3_1
    · exact s157_3_2
    · exact s157_3_3
    · exact s157_3_4
    · exact s157_3_5
    · exact s157_3_6
    · exact s157_3_7
  · fin_cases v
    · exact s157_4_0
    · exact s157_4_1
    · exact s157_4_2
    · exact s157_4_3
    · exact s157_4_4
    · exact s157_4_5
    · exact s157_4_6
    · exact s157_4_7
  · fin_cases v
    · exact s157_5_0
    · exact s157_5_1
    · exact s157_5_2
    · exact s157_5_3
    · exact s157_5_4
    · exact s157_5_5
    · exact s157_5_6
    · exact s157_5_7
  · exact List.all_eq_true.mp col157_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col157_7 v (List.mem_finRange v)
theorem col158_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 0 v) = true := by decide +kernel
theorem col158_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 1 v) = true := by decide +kernel
theorem s158_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 0 = true := by decide +kernel
theorem s158_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 1 = true := by decide +kernel
theorem s158_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 2 = true := by decide +kernel
theorem s158_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 3 = true := by decide +kernel
theorem k158_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k158_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k158_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s158_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k158_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k158_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k158_2_4_80 k h.1 (by omega)
theorem s158_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 5 = true := by decide +kernel
theorem s158_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 6 = true := by decide +kernel
theorem s158_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 2 7 = true := by decide +kernel
theorem s158_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 0 = true := by decide +kernel
theorem s158_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 1 = true := by decide +kernel
theorem s158_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 2 = true := by decide +kernel
theorem s158_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 3 = true := by decide +kernel
theorem k158_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k158_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k158_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s158_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k158_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k158_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k158_3_4_80 k h.1 (by omega)
theorem s158_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 5 = true := by decide +kernel
theorem s158_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 6 = true := by decide +kernel
theorem s158_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 3 7 = true := by decide +kernel
theorem s158_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 0 = true := by decide +kernel
theorem s158_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 1 = true := by decide +kernel
theorem s158_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 2 = true := by decide +kernel
theorem s158_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 3 = true := by decide +kernel
theorem k158_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k158_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k158_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k158_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k158_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k158_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k158_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k158_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k158_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k158_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k158_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k158_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k158_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k158_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k158_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k158_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k158_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k158_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k158_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k158_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k158_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s158_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k158_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k158_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k158_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k158_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k158_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k158_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k158_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k158_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k158_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k158_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k158_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k158_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k158_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k158_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k158_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k158_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k158_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k158_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k158_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k158_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k158_4_4_100 k h.1 (by omega)
theorem k158_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k158_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k158_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k158_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k158_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k158_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k158_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k158_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k158_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s158_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k158_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k158_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k158_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k158_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k158_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k158_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k158_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k158_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 158) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (158 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k158_4_5_40 k h.1 (by omega)
theorem k158_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k158_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k158_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k158_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k158_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k158_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k158_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k158_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k158_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k158_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k158_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s158_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k158_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k158_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k158_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k158_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k158_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k158_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k158_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k158_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k158_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k158_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TTsaaD 4 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k158_4_6_50 k h.1 (by omega)
theorem s158_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 4 7 = true := by decide +kernel
theorem s158_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 0 = true := by decide +kernel
theorem s158_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 1 = true := by decide +kernel
theorem s158_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 2 = true := by decide +kernel
theorem s158_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 3 = true := by decide +kernel
theorem s158_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 4 = true := by decide +kernel
theorem s158_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 5 = true := by decide +kernel
theorem k158_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k158_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k158_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k158_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k158_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k158_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s158_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k158_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k158_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k158_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k158_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k158_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 158) ((InDA2.TCasaD 5 5 6).getD (158 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k158_5_6_50 k h.1 (by omega)
theorem s158_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 5 7 = true := by decide +kernel
theorem col158_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 6 v) = true := by decide +kernel
theorem col158_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 7 v) = true := by decide +kernel
theorem col158 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 158) 158 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col158_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col158_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s158_2_0
    · exact s158_2_1
    · exact s158_2_2
    · exact s158_2_3
    · exact s158_2_4
    · exact s158_2_5
    · exact s158_2_6
    · exact s158_2_7
  · fin_cases v
    · exact s158_3_0
    · exact s158_3_1
    · exact s158_3_2
    · exact s158_3_3
    · exact s158_3_4
    · exact s158_3_5
    · exact s158_3_6
    · exact s158_3_7
  · fin_cases v
    · exact s158_4_0
    · exact s158_4_1
    · exact s158_4_2
    · exact s158_4_3
    · exact s158_4_4
    · exact s158_4_5
    · exact s158_4_6
    · exact s158_4_7
  · fin_cases v
    · exact s158_5_0
    · exact s158_5_1
    · exact s158_5_2
    · exact s158_5_3
    · exact s158_5_4
    · exact s158_5_5
    · exact s158_5_6
    · exact s158_5_7
  · exact List.all_eq_true.mp col158_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col158_7 v (List.mem_finRange v)
theorem col159_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 0 v) = true := by decide +kernel
theorem col159_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 1 v) = true := by decide +kernel
theorem s159_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 0 = true := by decide +kernel
theorem s159_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 1 = true := by decide +kernel
theorem s159_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 2 = true := by decide +kernel
theorem s159_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 3 = true := by decide +kernel
theorem k159_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k159_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k159_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s159_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k159_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k159_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k159_2_4_80 k h.1 (by omega)
theorem s159_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 5 = true := by decide +kernel
theorem s159_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 6 = true := by decide +kernel
theorem s159_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 2 7 = true := by decide +kernel
theorem s159_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 0 = true := by decide +kernel
theorem s159_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 1 = true := by decide +kernel
theorem s159_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 2 = true := by decide +kernel
theorem s159_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 3 = true := by decide +kernel
theorem k159_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k159_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k159_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s159_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k159_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k159_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k159_3_4_80 k h.1 (by omega)
theorem s159_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 5 = true := by decide +kernel
theorem s159_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 6 = true := by decide +kernel
theorem s159_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 3 7 = true := by decide +kernel
theorem s159_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 0 = true := by decide +kernel
theorem s159_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 1 = true := by decide +kernel
theorem s159_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 2 = true := by decide +kernel
theorem s159_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 3 = true := by decide +kernel
theorem k159_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k159_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k159_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k159_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k159_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k159_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k159_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k159_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k159_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k159_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k159_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k159_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k159_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k159_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k159_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k159_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k159_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k159_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k159_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k159_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k159_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s159_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k159_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k159_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k159_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k159_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k159_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k159_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k159_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k159_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k159_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k159_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k159_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k159_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k159_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k159_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k159_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k159_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k159_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k159_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k159_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k159_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k159_4_4_100 k h.1 (by omega)
theorem k159_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k159_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k159_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k159_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k159_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k159_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k159_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k159_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k159_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s159_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k159_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k159_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k159_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k159_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k159_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k159_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k159_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k159_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 159) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (159 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k159_4_5_40 k h.1 (by omega)
theorem k159_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k159_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k159_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k159_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k159_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k159_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k159_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k159_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k159_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k159_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k159_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s159_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k159_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k159_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k159_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k159_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k159_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k159_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k159_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k159_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k159_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k159_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TTsaaD 4 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k159_4_6_50 k h.1 (by omega)
theorem s159_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 4 7 = true := by decide +kernel
theorem s159_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 0 = true := by decide +kernel
theorem s159_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 1 = true := by decide +kernel
theorem s159_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 2 = true := by decide +kernel
theorem s159_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 3 = true := by decide +kernel
theorem s159_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 4 = true := by decide +kernel
theorem s159_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 5 = true := by decide +kernel
theorem k159_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k159_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k159_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k159_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k159_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k159_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s159_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k159_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k159_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k159_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k159_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k159_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 159) ((InDA2.TCasaD 5 5 6).getD (159 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k159_5_6_50 k h.1 (by omega)
theorem s159_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 5 7 = true := by decide +kernel
theorem col159_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 6 v) = true := by decide +kernel
theorem col159_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 7 v) = true := by decide +kernel
theorem col159 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 159) 159 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col159_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col159_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s159_2_0
    · exact s159_2_1
    · exact s159_2_2
    · exact s159_2_3
    · exact s159_2_4
    · exact s159_2_5
    · exact s159_2_6
    · exact s159_2_7
  · fin_cases v
    · exact s159_3_0
    · exact s159_3_1
    · exact s159_3_2
    · exact s159_3_3
    · exact s159_3_4
    · exact s159_3_5
    · exact s159_3_6
    · exact s159_3_7
  · fin_cases v
    · exact s159_4_0
    · exact s159_4_1
    · exact s159_4_2
    · exact s159_4_3
    · exact s159_4_4
    · exact s159_4_5
    · exact s159_4_6
    · exact s159_4_7
  · fin_cases v
    · exact s159_5_0
    · exact s159_5_1
    · exact s159_5_2
    · exact s159_5_3
    · exact s159_5_4
    · exact s159_5_5
    · exact s159_5_6
    · exact s159_5_7
  · exact List.all_eq_true.mp col159_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col159_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
