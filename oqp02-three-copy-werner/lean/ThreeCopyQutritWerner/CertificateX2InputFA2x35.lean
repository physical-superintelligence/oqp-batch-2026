module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [175, 180). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col175_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 0 v) = true := by decide +kernel
theorem col175_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 1 v) = true := by decide +kernel
theorem s175_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 0 = true := by decide +kernel
theorem s175_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 1 = true := by decide +kernel
theorem s175_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 2 = true := by decide +kernel
theorem s175_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 3 = true := by decide +kernel
theorem k175_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k175_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k175_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s175_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k175_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k175_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k175_2_4_80 k h.1 (by omega)
theorem s175_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 5 = true := by decide +kernel
theorem s175_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 6 = true := by decide +kernel
theorem s175_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 2 7 = true := by decide +kernel
theorem s175_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 0 = true := by decide +kernel
theorem s175_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 1 = true := by decide +kernel
theorem s175_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 2 = true := by decide +kernel
theorem s175_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 3 = true := by decide +kernel
theorem k175_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k175_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k175_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s175_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k175_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k175_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k175_3_4_80 k h.1 (by omega)
theorem s175_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 5 = true := by decide +kernel
theorem s175_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 6 = true := by decide +kernel
theorem s175_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 3 7 = true := by decide +kernel
theorem s175_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 0 = true := by decide +kernel
theorem s175_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 1 = true := by decide +kernel
theorem s175_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 2 = true := by decide +kernel
theorem s175_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 3 = true := by decide +kernel
theorem k175_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k175_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k175_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k175_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k175_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k175_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k175_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k175_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k175_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k175_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k175_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k175_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k175_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k175_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k175_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k175_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k175_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k175_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k175_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k175_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k175_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s175_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k175_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k175_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k175_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k175_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k175_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k175_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k175_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k175_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k175_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k175_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k175_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k175_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k175_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k175_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k175_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k175_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k175_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k175_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k175_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k175_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k175_4_4_100 k h.1 (by omega)
theorem k175_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k175_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k175_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k175_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k175_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k175_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k175_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k175_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k175_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s175_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k175_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k175_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k175_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k175_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k175_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k175_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k175_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k175_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 175) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (175 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k175_4_5_40 k h.1 (by omega)
theorem k175_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k175_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k175_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k175_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k175_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k175_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k175_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k175_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k175_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k175_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k175_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s175_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k175_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k175_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k175_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k175_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k175_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k175_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k175_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k175_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k175_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k175_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TTsaaD 4 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k175_4_6_50 k h.1 (by omega)
theorem s175_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 4 7 = true := by decide +kernel
theorem s175_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 0 = true := by decide +kernel
theorem s175_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 1 = true := by decide +kernel
theorem s175_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 2 = true := by decide +kernel
theorem s175_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 3 = true := by decide +kernel
theorem s175_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 4 = true := by decide +kernel
theorem s175_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 5 = true := by decide +kernel
theorem k175_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k175_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k175_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k175_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k175_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k175_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s175_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k175_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k175_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k175_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k175_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k175_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 175) ((InDA2.TCasaD 5 5 6).getD (175 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k175_5_6_50 k h.1 (by omega)
theorem s175_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 5 7 = true := by decide +kernel
theorem col175_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 6 v) = true := by decide +kernel
theorem col175_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 7 v) = true := by decide +kernel
theorem col175 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 175) 175 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col175_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col175_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s175_2_0
    · exact s175_2_1
    · exact s175_2_2
    · exact s175_2_3
    · exact s175_2_4
    · exact s175_2_5
    · exact s175_2_6
    · exact s175_2_7
  · fin_cases v
    · exact s175_3_0
    · exact s175_3_1
    · exact s175_3_2
    · exact s175_3_3
    · exact s175_3_4
    · exact s175_3_5
    · exact s175_3_6
    · exact s175_3_7
  · fin_cases v
    · exact s175_4_0
    · exact s175_4_1
    · exact s175_4_2
    · exact s175_4_3
    · exact s175_4_4
    · exact s175_4_5
    · exact s175_4_6
    · exact s175_4_7
  · fin_cases v
    · exact s175_5_0
    · exact s175_5_1
    · exact s175_5_2
    · exact s175_5_3
    · exact s175_5_4
    · exact s175_5_5
    · exact s175_5_6
    · exact s175_5_7
  · exact List.all_eq_true.mp col175_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col175_7 v (List.mem_finRange v)
theorem col176_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 0 v) = true := by decide +kernel
theorem col176_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 1 v) = true := by decide +kernel
theorem s176_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 0 = true := by decide +kernel
theorem s176_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 1 = true := by decide +kernel
theorem s176_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 2 = true := by decide +kernel
theorem s176_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 3 = true := by decide +kernel
theorem k176_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k176_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k176_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s176_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k176_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k176_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k176_2_4_80 k h.1 (by omega)
theorem s176_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 5 = true := by decide +kernel
theorem s176_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 6 = true := by decide +kernel
theorem s176_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 2 7 = true := by decide +kernel
theorem s176_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 0 = true := by decide +kernel
theorem s176_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 1 = true := by decide +kernel
theorem s176_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 2 = true := by decide +kernel
theorem s176_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 3 = true := by decide +kernel
theorem k176_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k176_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k176_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s176_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k176_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k176_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k176_3_4_80 k h.1 (by omega)
theorem s176_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 5 = true := by decide +kernel
theorem s176_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 6 = true := by decide +kernel
theorem s176_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 3 7 = true := by decide +kernel
theorem s176_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 0 = true := by decide +kernel
theorem s176_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 1 = true := by decide +kernel
theorem s176_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 2 = true := by decide +kernel
theorem s176_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 3 = true := by decide +kernel
theorem k176_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k176_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k176_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k176_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k176_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k176_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k176_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k176_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k176_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k176_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k176_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k176_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k176_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k176_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k176_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k176_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k176_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k176_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k176_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k176_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k176_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s176_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k176_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k176_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k176_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k176_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k176_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k176_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k176_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k176_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k176_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k176_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k176_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k176_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k176_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k176_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k176_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k176_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k176_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k176_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k176_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k176_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k176_4_4_100 k h.1 (by omega)
theorem k176_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k176_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k176_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k176_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k176_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k176_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k176_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k176_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k176_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s176_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k176_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k176_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k176_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k176_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k176_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k176_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k176_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k176_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k176_4_5_40 k h.1 (by omega)
theorem k176_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k176_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k176_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k176_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k176_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k176_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k176_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k176_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k176_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k176_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k176_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s176_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k176_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k176_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k176_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k176_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k176_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k176_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k176_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k176_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k176_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k176_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k176_4_6_50 k h.1 (by omega)
theorem s176_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 4 7 = true := by decide +kernel
theorem s176_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 0 = true := by decide +kernel
theorem s176_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 1 = true := by decide +kernel
theorem s176_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 2 = true := by decide +kernel
theorem s176_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 3 = true := by decide +kernel
theorem k176_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k176_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k176_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k176_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k176_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k176_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k176_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k176_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k176_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k176_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k176_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s176_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k176_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k176_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k176_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k176_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k176_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k176_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k176_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k176_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k176_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k176_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k176_5_4_100 k h.1 (by omega)
theorem k176_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k176_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k176_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k176_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k176_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s176_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k176_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k176_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k176_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k176_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k176_5_5_40 k h.1 (by omega)
theorem k176_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k176_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k176_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k176_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k176_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k176_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s176_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k176_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k176_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k176_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k176_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k176_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 176) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (176 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k176_5_6_50 k h.1 (by omega)
theorem s176_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 5 7 = true := by decide +kernel
theorem col176_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 6 v) = true := by decide +kernel
theorem col176_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 7 v) = true := by decide +kernel
theorem col176 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 176) 176 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col176_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col176_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s176_2_0
    · exact s176_2_1
    · exact s176_2_2
    · exact s176_2_3
    · exact s176_2_4
    · exact s176_2_5
    · exact s176_2_6
    · exact s176_2_7
  · fin_cases v
    · exact s176_3_0
    · exact s176_3_1
    · exact s176_3_2
    · exact s176_3_3
    · exact s176_3_4
    · exact s176_3_5
    · exact s176_3_6
    · exact s176_3_7
  · fin_cases v
    · exact s176_4_0
    · exact s176_4_1
    · exact s176_4_2
    · exact s176_4_3
    · exact s176_4_4
    · exact s176_4_5
    · exact s176_4_6
    · exact s176_4_7
  · fin_cases v
    · exact s176_5_0
    · exact s176_5_1
    · exact s176_5_2
    · exact s176_5_3
    · exact s176_5_4
    · exact s176_5_5
    · exact s176_5_6
    · exact s176_5_7
  · exact List.all_eq_true.mp col176_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col176_7 v (List.mem_finRange v)
theorem col177_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 0 v) = true := by decide +kernel
theorem col177_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 1 v) = true := by decide +kernel
theorem s177_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 0 = true := by decide +kernel
theorem s177_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 1 = true := by decide +kernel
theorem s177_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 2 = true := by decide +kernel
theorem s177_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 3 = true := by decide +kernel
theorem k177_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k177_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k177_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s177_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k177_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k177_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k177_2_4_80 k h.1 (by omega)
theorem s177_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 5 = true := by decide +kernel
theorem s177_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 6 = true := by decide +kernel
theorem s177_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 2 7 = true := by decide +kernel
theorem s177_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 0 = true := by decide +kernel
theorem s177_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 1 = true := by decide +kernel
theorem s177_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 2 = true := by decide +kernel
theorem s177_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 3 = true := by decide +kernel
theorem k177_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k177_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k177_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s177_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k177_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k177_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k177_3_4_80 k h.1 (by omega)
theorem s177_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 5 = true := by decide +kernel
theorem s177_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 6 = true := by decide +kernel
theorem s177_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 3 7 = true := by decide +kernel
theorem s177_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 0 = true := by decide +kernel
theorem s177_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 1 = true := by decide +kernel
theorem s177_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 2 = true := by decide +kernel
theorem s177_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 3 = true := by decide +kernel
theorem k177_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k177_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k177_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k177_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k177_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k177_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k177_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k177_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k177_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k177_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k177_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k177_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k177_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k177_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k177_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k177_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k177_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k177_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k177_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k177_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k177_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s177_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k177_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k177_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k177_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k177_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k177_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k177_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k177_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k177_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k177_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k177_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k177_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k177_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k177_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k177_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k177_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k177_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k177_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k177_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k177_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k177_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k177_4_4_100 k h.1 (by omega)
theorem k177_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k177_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k177_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k177_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k177_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k177_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k177_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k177_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k177_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s177_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k177_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k177_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k177_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k177_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k177_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k177_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k177_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k177_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k177_4_5_40 k h.1 (by omega)
theorem k177_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k177_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k177_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k177_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k177_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k177_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k177_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k177_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k177_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k177_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k177_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s177_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k177_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k177_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k177_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k177_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k177_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k177_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k177_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k177_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k177_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k177_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k177_4_6_50 k h.1 (by omega)
theorem s177_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 4 7 = true := by decide +kernel
theorem s177_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 0 = true := by decide +kernel
theorem s177_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 1 = true := by decide +kernel
theorem s177_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 2 = true := by decide +kernel
theorem s177_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 3 = true := by decide +kernel
theorem k177_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k177_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k177_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k177_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k177_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k177_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k177_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k177_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k177_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k177_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k177_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s177_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k177_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k177_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k177_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k177_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k177_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k177_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k177_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k177_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k177_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k177_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k177_5_4_100 k h.1 (by omega)
theorem k177_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k177_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k177_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k177_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k177_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s177_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k177_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k177_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k177_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k177_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k177_5_5_40 k h.1 (by omega)
theorem k177_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k177_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k177_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k177_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k177_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k177_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s177_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k177_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k177_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k177_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k177_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k177_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 177) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (177 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k177_5_6_50 k h.1 (by omega)
theorem s177_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 5 7 = true := by decide +kernel
theorem col177_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 6 v) = true := by decide +kernel
theorem col177_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 7 v) = true := by decide +kernel
theorem col177 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 177) 177 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col177_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col177_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s177_2_0
    · exact s177_2_1
    · exact s177_2_2
    · exact s177_2_3
    · exact s177_2_4
    · exact s177_2_5
    · exact s177_2_6
    · exact s177_2_7
  · fin_cases v
    · exact s177_3_0
    · exact s177_3_1
    · exact s177_3_2
    · exact s177_3_3
    · exact s177_3_4
    · exact s177_3_5
    · exact s177_3_6
    · exact s177_3_7
  · fin_cases v
    · exact s177_4_0
    · exact s177_4_1
    · exact s177_4_2
    · exact s177_4_3
    · exact s177_4_4
    · exact s177_4_5
    · exact s177_4_6
    · exact s177_4_7
  · fin_cases v
    · exact s177_5_0
    · exact s177_5_1
    · exact s177_5_2
    · exact s177_5_3
    · exact s177_5_4
    · exact s177_5_5
    · exact s177_5_6
    · exact s177_5_7
  · exact List.all_eq_true.mp col177_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col177_7 v (List.mem_finRange v)
theorem col178_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 0 v) = true := by decide +kernel
theorem col178_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 1 v) = true := by decide +kernel
theorem s178_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 0 = true := by decide +kernel
theorem s178_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 1 = true := by decide +kernel
theorem s178_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 2 = true := by decide +kernel
theorem s178_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 3 = true := by decide +kernel
theorem k178_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k178_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k178_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s178_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k178_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k178_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k178_2_4_80 k h.1 (by omega)
theorem s178_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 5 = true := by decide +kernel
theorem s178_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 6 = true := by decide +kernel
theorem s178_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 2 7 = true := by decide +kernel
theorem s178_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 0 = true := by decide +kernel
theorem s178_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 1 = true := by decide +kernel
theorem s178_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 2 = true := by decide +kernel
theorem s178_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 3 = true := by decide +kernel
theorem k178_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k178_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k178_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s178_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k178_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k178_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k178_3_4_80 k h.1 (by omega)
theorem s178_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 5 = true := by decide +kernel
theorem s178_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 6 = true := by decide +kernel
theorem s178_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 3 7 = true := by decide +kernel
theorem s178_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 0 = true := by decide +kernel
theorem s178_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 1 = true := by decide +kernel
theorem s178_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 2 = true := by decide +kernel
theorem s178_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 3 = true := by decide +kernel
theorem k178_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k178_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k178_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k178_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k178_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k178_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k178_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k178_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k178_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k178_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k178_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k178_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k178_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k178_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k178_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k178_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k178_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k178_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k178_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k178_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k178_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s178_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k178_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k178_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k178_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k178_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k178_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k178_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k178_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k178_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k178_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k178_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k178_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k178_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k178_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k178_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k178_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k178_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k178_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k178_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k178_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k178_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k178_4_4_100 k h.1 (by omega)
theorem k178_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k178_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k178_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k178_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k178_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k178_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k178_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k178_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k178_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s178_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k178_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k178_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k178_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k178_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k178_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k178_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k178_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k178_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k178_4_5_40 k h.1 (by omega)
theorem k178_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k178_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k178_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k178_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k178_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k178_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k178_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k178_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k178_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k178_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k178_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s178_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k178_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k178_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k178_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k178_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k178_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k178_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k178_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k178_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k178_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k178_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k178_4_6_50 k h.1 (by omega)
theorem s178_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 4 7 = true := by decide +kernel
theorem s178_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 0 = true := by decide +kernel
theorem s178_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 1 = true := by decide +kernel
theorem s178_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 2 = true := by decide +kernel
theorem s178_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 3 = true := by decide +kernel
theorem k178_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k178_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k178_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k178_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k178_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k178_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k178_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k178_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k178_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k178_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k178_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s178_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k178_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k178_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k178_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k178_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k178_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k178_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k178_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k178_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k178_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k178_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k178_5_4_100 k h.1 (by omega)
theorem k178_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k178_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k178_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k178_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k178_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s178_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k178_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k178_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k178_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k178_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k178_5_5_40 k h.1 (by omega)
theorem k178_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k178_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k178_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k178_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k178_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k178_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s178_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k178_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k178_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k178_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k178_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k178_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 178) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (178 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k178_5_6_50 k h.1 (by omega)
theorem s178_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 5 7 = true := by decide +kernel
theorem col178_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 6 v) = true := by decide +kernel
theorem col178_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 7 v) = true := by decide +kernel
theorem col178 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 178) 178 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col178_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col178_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s178_2_0
    · exact s178_2_1
    · exact s178_2_2
    · exact s178_2_3
    · exact s178_2_4
    · exact s178_2_5
    · exact s178_2_6
    · exact s178_2_7
  · fin_cases v
    · exact s178_3_0
    · exact s178_3_1
    · exact s178_3_2
    · exact s178_3_3
    · exact s178_3_4
    · exact s178_3_5
    · exact s178_3_6
    · exact s178_3_7
  · fin_cases v
    · exact s178_4_0
    · exact s178_4_1
    · exact s178_4_2
    · exact s178_4_3
    · exact s178_4_4
    · exact s178_4_5
    · exact s178_4_6
    · exact s178_4_7
  · fin_cases v
    · exact s178_5_0
    · exact s178_5_1
    · exact s178_5_2
    · exact s178_5_3
    · exact s178_5_4
    · exact s178_5_5
    · exact s178_5_6
    · exact s178_5_7
  · exact List.all_eq_true.mp col178_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col178_7 v (List.mem_finRange v)
theorem col179_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 0 v) = true := by decide +kernel
theorem col179_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 1 v) = true := by decide +kernel
theorem s179_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 0 = true := by decide +kernel
theorem s179_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 1 = true := by decide +kernel
theorem s179_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 2 = true := by decide +kernel
theorem s179_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 3 = true := by decide +kernel
theorem k179_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k179_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k179_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s179_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k179_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k179_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k179_2_4_80 k h.1 (by omega)
theorem s179_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 5 = true := by decide +kernel
theorem s179_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 6 = true := by decide +kernel
theorem s179_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 2 7 = true := by decide +kernel
theorem s179_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 0 = true := by decide +kernel
theorem s179_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 1 = true := by decide +kernel
theorem s179_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 2 = true := by decide +kernel
theorem s179_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 3 = true := by decide +kernel
theorem k179_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k179_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k179_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s179_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k179_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k179_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k179_3_4_80 k h.1 (by omega)
theorem s179_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 5 = true := by decide +kernel
theorem s179_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 6 = true := by decide +kernel
theorem s179_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 3 7 = true := by decide +kernel
theorem s179_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 0 = true := by decide +kernel
theorem s179_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 1 = true := by decide +kernel
theorem s179_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 2 = true := by decide +kernel
theorem s179_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 3 = true := by decide +kernel
theorem k179_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k179_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k179_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k179_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k179_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k179_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k179_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k179_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k179_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k179_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k179_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k179_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k179_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k179_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k179_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k179_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k179_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k179_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k179_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k179_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k179_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s179_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k179_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k179_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k179_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k179_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k179_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k179_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k179_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k179_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k179_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k179_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k179_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k179_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k179_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k179_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k179_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k179_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k179_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k179_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k179_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k179_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k179_4_4_100 k h.1 (by omega)
theorem k179_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k179_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k179_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k179_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k179_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k179_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k179_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k179_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k179_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s179_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k179_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k179_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k179_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k179_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k179_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k179_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k179_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k179_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k179_4_5_40 k h.1 (by omega)
theorem k179_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k179_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k179_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k179_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k179_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k179_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k179_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k179_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k179_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k179_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k179_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s179_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k179_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k179_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k179_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k179_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k179_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k179_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k179_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k179_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k179_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k179_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k179_4_6_50 k h.1 (by omega)
theorem s179_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 4 7 = true := by decide +kernel
theorem s179_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 0 = true := by decide +kernel
theorem s179_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 1 = true := by decide +kernel
theorem s179_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 2 = true := by decide +kernel
theorem s179_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 3 = true := by decide +kernel
theorem k179_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k179_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k179_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k179_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k179_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k179_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k179_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k179_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k179_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k179_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k179_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s179_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k179_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k179_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k179_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k179_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k179_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k179_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k179_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k179_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k179_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k179_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k179_5_4_100 k h.1 (by omega)
theorem k179_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k179_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k179_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k179_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k179_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s179_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k179_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k179_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k179_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k179_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k179_5_5_40 k h.1 (by omega)
theorem k179_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k179_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k179_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k179_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k179_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k179_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s179_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k179_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k179_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k179_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k179_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k179_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 179) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (179 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k179_5_6_50 k h.1 (by omega)
theorem s179_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 5 7 = true := by decide +kernel
theorem col179_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 6 v) = true := by decide +kernel
theorem col179_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 7 v) = true := by decide +kernel
theorem col179 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 179) 179 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col179_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col179_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s179_2_0
    · exact s179_2_1
    · exact s179_2_2
    · exact s179_2_3
    · exact s179_2_4
    · exact s179_2_5
    · exact s179_2_6
    · exact s179_2_7
  · fin_cases v
    · exact s179_3_0
    · exact s179_3_1
    · exact s179_3_2
    · exact s179_3_3
    · exact s179_3_4
    · exact s179_3_5
    · exact s179_3_6
    · exact s179_3_7
  · fin_cases v
    · exact s179_4_0
    · exact s179_4_1
    · exact s179_4_2
    · exact s179_4_3
    · exact s179_4_4
    · exact s179_4_5
    · exact s179_4_6
    · exact s179_4_7
  · fin_cases v
    · exact s179_5_0
    · exact s179_5_1
    · exact s179_5_2
    · exact s179_5_3
    · exact s179_5_4
    · exact s179_5_5
    · exact s179_5_6
    · exact s179_5_7
  · exact List.all_eq_true.mp col179_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col179_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
