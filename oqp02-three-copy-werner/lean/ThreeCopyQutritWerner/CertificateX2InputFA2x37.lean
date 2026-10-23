module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [185, 190). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col185_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 0 v) = true := by decide +kernel
theorem col185_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 1 v) = true := by decide +kernel
theorem s185_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 0 = true := by decide +kernel
theorem s185_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 1 = true := by decide +kernel
theorem s185_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 2 = true := by decide +kernel
theorem s185_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 3 = true := by decide +kernel
theorem k185_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k185_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k185_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s185_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k185_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k185_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k185_2_4_80 k h.1 (by omega)
theorem s185_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 5 = true := by decide +kernel
theorem s185_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 6 = true := by decide +kernel
theorem s185_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 2 7 = true := by decide +kernel
theorem s185_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 0 = true := by decide +kernel
theorem s185_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 1 = true := by decide +kernel
theorem s185_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 2 = true := by decide +kernel
theorem s185_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 3 = true := by decide +kernel
theorem k185_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k185_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k185_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s185_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k185_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k185_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k185_3_4_80 k h.1 (by omega)
theorem s185_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 5 = true := by decide +kernel
theorem s185_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 6 = true := by decide +kernel
theorem s185_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 3 7 = true := by decide +kernel
theorem s185_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 0 = true := by decide +kernel
theorem s185_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 1 = true := by decide +kernel
theorem s185_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 2 = true := by decide +kernel
theorem s185_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 3 = true := by decide +kernel
theorem k185_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k185_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k185_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k185_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k185_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k185_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k185_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k185_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k185_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k185_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k185_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k185_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k185_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k185_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k185_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k185_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k185_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k185_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k185_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k185_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k185_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s185_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k185_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k185_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k185_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k185_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k185_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k185_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k185_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k185_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k185_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k185_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k185_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k185_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k185_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k185_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k185_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k185_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k185_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k185_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k185_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k185_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k185_4_4_100 k h.1 (by omega)
theorem k185_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k185_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k185_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k185_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k185_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k185_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k185_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k185_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k185_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s185_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k185_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k185_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k185_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k185_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k185_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k185_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k185_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k185_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k185_4_5_40 k h.1 (by omega)
theorem k185_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k185_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k185_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k185_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k185_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k185_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k185_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k185_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k185_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k185_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k185_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s185_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k185_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k185_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k185_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k185_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k185_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k185_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k185_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k185_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k185_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k185_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k185_4_6_50 k h.1 (by omega)
theorem s185_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 4 7 = true := by decide +kernel
theorem s185_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 0 = true := by decide +kernel
theorem s185_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 1 = true := by decide +kernel
theorem s185_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 2 = true := by decide +kernel
theorem s185_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 3 = true := by decide +kernel
theorem k185_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k185_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k185_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k185_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k185_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k185_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k185_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k185_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k185_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k185_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k185_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s185_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k185_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k185_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k185_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k185_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k185_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k185_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k185_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k185_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k185_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k185_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k185_5_4_100 k h.1 (by omega)
theorem k185_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k185_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k185_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k185_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k185_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s185_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k185_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k185_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k185_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k185_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k185_5_5_40 k h.1 (by omega)
theorem k185_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k185_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k185_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k185_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k185_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k185_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s185_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k185_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k185_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k185_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k185_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k185_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 185) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (185 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k185_5_6_50 k h.1 (by omega)
theorem s185_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 5 7 = true := by decide +kernel
theorem col185_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 6 v) = true := by decide +kernel
theorem col185_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 7 v) = true := by decide +kernel
theorem col185 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 185) 185 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col185_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col185_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s185_2_0
    · exact s185_2_1
    · exact s185_2_2
    · exact s185_2_3
    · exact s185_2_4
    · exact s185_2_5
    · exact s185_2_6
    · exact s185_2_7
  · fin_cases v
    · exact s185_3_0
    · exact s185_3_1
    · exact s185_3_2
    · exact s185_3_3
    · exact s185_3_4
    · exact s185_3_5
    · exact s185_3_6
    · exact s185_3_7
  · fin_cases v
    · exact s185_4_0
    · exact s185_4_1
    · exact s185_4_2
    · exact s185_4_3
    · exact s185_4_4
    · exact s185_4_5
    · exact s185_4_6
    · exact s185_4_7
  · fin_cases v
    · exact s185_5_0
    · exact s185_5_1
    · exact s185_5_2
    · exact s185_5_3
    · exact s185_5_4
    · exact s185_5_5
    · exact s185_5_6
    · exact s185_5_7
  · exact List.all_eq_true.mp col185_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col185_7 v (List.mem_finRange v)
theorem col186_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 0 v) = true := by decide +kernel
theorem col186_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 1 v) = true := by decide +kernel
theorem s186_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 0 = true := by decide +kernel
theorem s186_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 1 = true := by decide +kernel
theorem s186_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 2 = true := by decide +kernel
theorem s186_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 3 = true := by decide +kernel
theorem k186_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k186_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k186_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s186_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k186_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k186_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k186_2_4_80 k h.1 (by omega)
theorem s186_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 5 = true := by decide +kernel
theorem s186_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 6 = true := by decide +kernel
theorem s186_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 2 7 = true := by decide +kernel
theorem s186_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 0 = true := by decide +kernel
theorem s186_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 1 = true := by decide +kernel
theorem s186_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 2 = true := by decide +kernel
theorem s186_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 3 = true := by decide +kernel
theorem k186_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k186_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k186_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s186_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k186_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k186_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k186_3_4_80 k h.1 (by omega)
theorem s186_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 5 = true := by decide +kernel
theorem s186_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 6 = true := by decide +kernel
theorem s186_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 3 7 = true := by decide +kernel
theorem s186_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 0 = true := by decide +kernel
theorem s186_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 1 = true := by decide +kernel
theorem s186_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 2 = true := by decide +kernel
theorem s186_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 3 = true := by decide +kernel
theorem k186_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k186_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k186_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k186_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k186_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k186_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k186_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k186_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k186_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k186_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k186_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k186_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k186_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k186_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k186_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k186_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k186_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k186_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k186_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k186_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k186_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s186_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k186_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k186_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k186_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k186_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k186_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k186_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k186_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k186_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k186_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k186_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k186_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k186_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k186_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k186_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k186_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k186_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k186_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k186_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k186_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k186_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k186_4_4_100 k h.1 (by omega)
theorem k186_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k186_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k186_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k186_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k186_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k186_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k186_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k186_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k186_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s186_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k186_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k186_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k186_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k186_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k186_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k186_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k186_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k186_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k186_4_5_40 k h.1 (by omega)
theorem k186_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k186_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k186_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k186_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k186_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k186_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k186_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k186_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k186_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k186_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k186_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s186_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k186_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k186_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k186_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k186_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k186_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k186_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k186_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k186_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k186_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k186_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k186_4_6_50 k h.1 (by omega)
theorem s186_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 4 7 = true := by decide +kernel
theorem s186_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 0 = true := by decide +kernel
theorem s186_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 1 = true := by decide +kernel
theorem s186_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 2 = true := by decide +kernel
theorem s186_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 3 = true := by decide +kernel
theorem k186_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k186_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k186_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k186_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k186_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k186_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k186_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k186_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k186_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k186_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k186_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s186_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k186_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k186_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k186_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k186_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k186_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k186_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k186_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k186_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k186_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k186_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k186_5_4_100 k h.1 (by omega)
theorem k186_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k186_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k186_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k186_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k186_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s186_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k186_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k186_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k186_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k186_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k186_5_5_40 k h.1 (by omega)
theorem k186_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k186_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k186_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k186_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k186_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k186_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s186_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k186_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k186_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k186_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k186_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k186_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 186) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (186 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k186_5_6_50 k h.1 (by omega)
theorem s186_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 5 7 = true := by decide +kernel
theorem col186_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 6 v) = true := by decide +kernel
theorem col186_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 7 v) = true := by decide +kernel
theorem col186 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 186) 186 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col186_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col186_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s186_2_0
    · exact s186_2_1
    · exact s186_2_2
    · exact s186_2_3
    · exact s186_2_4
    · exact s186_2_5
    · exact s186_2_6
    · exact s186_2_7
  · fin_cases v
    · exact s186_3_0
    · exact s186_3_1
    · exact s186_3_2
    · exact s186_3_3
    · exact s186_3_4
    · exact s186_3_5
    · exact s186_3_6
    · exact s186_3_7
  · fin_cases v
    · exact s186_4_0
    · exact s186_4_1
    · exact s186_4_2
    · exact s186_4_3
    · exact s186_4_4
    · exact s186_4_5
    · exact s186_4_6
    · exact s186_4_7
  · fin_cases v
    · exact s186_5_0
    · exact s186_5_1
    · exact s186_5_2
    · exact s186_5_3
    · exact s186_5_4
    · exact s186_5_5
    · exact s186_5_6
    · exact s186_5_7
  · exact List.all_eq_true.mp col186_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col186_7 v (List.mem_finRange v)
theorem col187_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 0 v) = true := by decide +kernel
theorem col187_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 1 v) = true := by decide +kernel
theorem s187_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 0 = true := by decide +kernel
theorem s187_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 1 = true := by decide +kernel
theorem s187_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 2 = true := by decide +kernel
theorem s187_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 3 = true := by decide +kernel
theorem k187_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k187_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k187_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s187_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k187_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k187_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k187_2_4_80 k h.1 (by omega)
theorem s187_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 5 = true := by decide +kernel
theorem s187_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 6 = true := by decide +kernel
theorem s187_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 2 7 = true := by decide +kernel
theorem s187_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 0 = true := by decide +kernel
theorem s187_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 1 = true := by decide +kernel
theorem s187_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 2 = true := by decide +kernel
theorem s187_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 3 = true := by decide +kernel
theorem k187_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k187_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k187_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s187_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k187_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k187_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k187_3_4_80 k h.1 (by omega)
theorem s187_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 5 = true := by decide +kernel
theorem s187_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 6 = true := by decide +kernel
theorem s187_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 3 7 = true := by decide +kernel
theorem s187_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 0 = true := by decide +kernel
theorem s187_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 1 = true := by decide +kernel
theorem s187_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 2 = true := by decide +kernel
theorem s187_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 3 = true := by decide +kernel
theorem k187_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k187_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k187_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k187_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k187_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k187_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k187_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k187_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k187_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k187_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k187_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k187_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k187_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k187_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k187_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k187_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k187_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k187_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k187_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k187_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k187_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s187_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k187_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k187_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k187_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k187_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k187_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k187_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k187_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k187_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k187_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k187_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k187_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k187_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k187_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k187_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k187_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k187_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k187_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k187_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k187_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k187_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k187_4_4_100 k h.1 (by omega)
theorem k187_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k187_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k187_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k187_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k187_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k187_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k187_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k187_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k187_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s187_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k187_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k187_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k187_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k187_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k187_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k187_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k187_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k187_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k187_4_5_40 k h.1 (by omega)
theorem k187_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k187_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k187_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k187_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k187_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k187_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k187_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k187_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k187_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k187_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k187_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s187_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k187_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k187_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k187_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k187_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k187_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k187_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k187_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k187_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k187_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k187_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k187_4_6_50 k h.1 (by omega)
theorem s187_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 4 7 = true := by decide +kernel
theorem s187_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 0 = true := by decide +kernel
theorem s187_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 1 = true := by decide +kernel
theorem s187_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 2 = true := by decide +kernel
theorem s187_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 3 = true := by decide +kernel
theorem k187_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k187_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k187_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k187_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k187_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k187_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k187_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k187_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k187_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k187_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k187_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s187_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k187_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k187_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k187_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k187_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k187_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k187_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k187_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k187_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k187_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k187_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k187_5_4_100 k h.1 (by omega)
theorem k187_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k187_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k187_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k187_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k187_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s187_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k187_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k187_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k187_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k187_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k187_5_5_40 k h.1 (by omega)
theorem k187_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k187_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k187_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k187_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k187_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k187_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s187_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k187_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k187_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k187_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k187_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k187_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 187) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (187 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k187_5_6_50 k h.1 (by omega)
theorem s187_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 5 7 = true := by decide +kernel
theorem col187_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 6 v) = true := by decide +kernel
theorem col187_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 7 v) = true := by decide +kernel
theorem col187 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 187) 187 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col187_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col187_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s187_2_0
    · exact s187_2_1
    · exact s187_2_2
    · exact s187_2_3
    · exact s187_2_4
    · exact s187_2_5
    · exact s187_2_6
    · exact s187_2_7
  · fin_cases v
    · exact s187_3_0
    · exact s187_3_1
    · exact s187_3_2
    · exact s187_3_3
    · exact s187_3_4
    · exact s187_3_5
    · exact s187_3_6
    · exact s187_3_7
  · fin_cases v
    · exact s187_4_0
    · exact s187_4_1
    · exact s187_4_2
    · exact s187_4_3
    · exact s187_4_4
    · exact s187_4_5
    · exact s187_4_6
    · exact s187_4_7
  · fin_cases v
    · exact s187_5_0
    · exact s187_5_1
    · exact s187_5_2
    · exact s187_5_3
    · exact s187_5_4
    · exact s187_5_5
    · exact s187_5_6
    · exact s187_5_7
  · exact List.all_eq_true.mp col187_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col187_7 v (List.mem_finRange v)
theorem col188_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 0 v) = true := by decide +kernel
theorem col188_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 1 v) = true := by decide +kernel
theorem s188_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 0 = true := by decide +kernel
theorem s188_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 1 = true := by decide +kernel
theorem s188_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 2 = true := by decide +kernel
theorem s188_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 3 = true := by decide +kernel
theorem k188_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k188_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k188_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s188_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k188_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k188_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k188_2_4_80 k h.1 (by omega)
theorem s188_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 5 = true := by decide +kernel
theorem s188_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 6 = true := by decide +kernel
theorem s188_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 2 7 = true := by decide +kernel
theorem s188_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 0 = true := by decide +kernel
theorem s188_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 1 = true := by decide +kernel
theorem s188_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 2 = true := by decide +kernel
theorem s188_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 3 = true := by decide +kernel
theorem k188_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k188_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k188_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s188_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k188_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k188_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k188_3_4_80 k h.1 (by omega)
theorem s188_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 5 = true := by decide +kernel
theorem s188_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 6 = true := by decide +kernel
theorem s188_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 3 7 = true := by decide +kernel
theorem s188_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 0 = true := by decide +kernel
theorem s188_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 1 = true := by decide +kernel
theorem s188_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 2 = true := by decide +kernel
theorem s188_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 3 = true := by decide +kernel
theorem k188_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k188_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k188_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k188_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k188_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k188_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k188_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k188_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k188_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k188_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k188_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k188_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k188_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k188_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k188_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k188_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k188_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k188_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k188_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k188_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k188_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s188_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k188_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k188_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k188_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k188_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k188_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k188_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k188_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k188_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k188_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k188_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k188_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k188_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k188_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k188_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k188_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k188_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k188_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k188_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k188_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k188_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k188_4_4_100 k h.1 (by omega)
theorem k188_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k188_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k188_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k188_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k188_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k188_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k188_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k188_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k188_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s188_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k188_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k188_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k188_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k188_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k188_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k188_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k188_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k188_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k188_4_5_40 k h.1 (by omega)
theorem k188_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k188_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k188_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k188_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k188_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k188_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k188_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k188_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k188_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k188_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k188_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s188_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k188_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k188_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k188_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k188_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k188_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k188_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k188_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k188_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k188_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k188_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k188_4_6_50 k h.1 (by omega)
theorem s188_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 4 7 = true := by decide +kernel
theorem s188_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 0 = true := by decide +kernel
theorem s188_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 1 = true := by decide +kernel
theorem s188_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 2 = true := by decide +kernel
theorem s188_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 3 = true := by decide +kernel
theorem k188_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k188_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k188_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k188_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k188_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k188_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k188_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k188_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k188_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k188_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k188_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s188_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k188_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k188_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k188_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k188_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k188_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k188_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k188_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k188_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k188_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k188_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k188_5_4_100 k h.1 (by omega)
theorem k188_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k188_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k188_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k188_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k188_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s188_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k188_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k188_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k188_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k188_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k188_5_5_40 k h.1 (by omega)
theorem k188_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k188_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k188_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k188_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k188_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k188_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s188_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k188_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k188_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k188_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k188_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k188_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 188) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (188 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k188_5_6_50 k h.1 (by omega)
theorem s188_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 5 7 = true := by decide +kernel
theorem col188_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 6 v) = true := by decide +kernel
theorem col188_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 7 v) = true := by decide +kernel
theorem col188 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 188) 188 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col188_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col188_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s188_2_0
    · exact s188_2_1
    · exact s188_2_2
    · exact s188_2_3
    · exact s188_2_4
    · exact s188_2_5
    · exact s188_2_6
    · exact s188_2_7
  · fin_cases v
    · exact s188_3_0
    · exact s188_3_1
    · exact s188_3_2
    · exact s188_3_3
    · exact s188_3_4
    · exact s188_3_5
    · exact s188_3_6
    · exact s188_3_7
  · fin_cases v
    · exact s188_4_0
    · exact s188_4_1
    · exact s188_4_2
    · exact s188_4_3
    · exact s188_4_4
    · exact s188_4_5
    · exact s188_4_6
    · exact s188_4_7
  · fin_cases v
    · exact s188_5_0
    · exact s188_5_1
    · exact s188_5_2
    · exact s188_5_3
    · exact s188_5_4
    · exact s188_5_5
    · exact s188_5_6
    · exact s188_5_7
  · exact List.all_eq_true.mp col188_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col188_7 v (List.mem_finRange v)
theorem col189_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 0 v) = true := by decide +kernel
theorem col189_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 1 v) = true := by decide +kernel
theorem s189_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 0 = true := by decide +kernel
theorem s189_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 1 = true := by decide +kernel
theorem s189_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 2 = true := by decide +kernel
theorem s189_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 3 = true := by decide +kernel
theorem k189_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k189_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k189_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s189_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k189_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k189_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k189_2_4_80 k h.1 (by omega)
theorem s189_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 5 = true := by decide +kernel
theorem s189_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 6 = true := by decide +kernel
theorem s189_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 2 7 = true := by decide +kernel
theorem s189_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 0 = true := by decide +kernel
theorem s189_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 1 = true := by decide +kernel
theorem s189_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 2 = true := by decide +kernel
theorem s189_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 3 = true := by decide +kernel
theorem k189_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k189_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k189_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s189_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k189_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k189_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k189_3_4_80 k h.1 (by omega)
theorem s189_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 5 = true := by decide +kernel
theorem s189_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 6 = true := by decide +kernel
theorem s189_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 3 7 = true := by decide +kernel
theorem s189_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 0 = true := by decide +kernel
theorem s189_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 1 = true := by decide +kernel
theorem s189_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 2 = true := by decide +kernel
theorem s189_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 3 = true := by decide +kernel
theorem k189_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k189_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k189_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k189_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k189_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k189_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k189_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k189_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k189_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k189_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k189_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k189_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k189_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k189_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k189_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k189_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k189_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k189_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k189_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k189_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k189_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s189_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k189_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k189_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k189_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k189_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k189_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k189_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k189_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k189_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k189_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k189_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k189_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k189_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k189_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k189_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k189_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k189_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k189_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k189_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k189_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k189_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k189_4_4_100 k h.1 (by omega)
theorem k189_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k189_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k189_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k189_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k189_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k189_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k189_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k189_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k189_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s189_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k189_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k189_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k189_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k189_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k189_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k189_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k189_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k189_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k189_4_5_40 k h.1 (by omega)
theorem k189_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k189_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k189_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k189_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k189_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k189_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k189_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k189_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k189_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k189_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k189_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s189_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k189_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k189_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k189_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k189_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k189_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k189_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k189_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k189_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k189_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k189_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k189_4_6_50 k h.1 (by omega)
theorem s189_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 4 7 = true := by decide +kernel
theorem s189_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 0 = true := by decide +kernel
theorem s189_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 1 = true := by decide +kernel
theorem s189_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 2 = true := by decide +kernel
theorem s189_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 3 = true := by decide +kernel
theorem k189_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k189_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k189_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k189_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k189_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k189_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k189_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k189_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k189_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k189_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k189_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s189_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k189_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k189_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k189_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k189_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k189_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k189_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k189_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k189_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k189_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k189_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k189_5_4_100 k h.1 (by omega)
theorem k189_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k189_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k189_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k189_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k189_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s189_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k189_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k189_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k189_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k189_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k189_5_5_40 k h.1 (by omega)
theorem k189_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k189_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k189_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k189_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k189_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k189_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s189_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k189_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k189_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k189_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k189_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k189_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 189) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (189 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k189_5_6_50 k h.1 (by omega)
theorem s189_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 5 7 = true := by decide +kernel
theorem col189_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 6 v) = true := by decide +kernel
theorem col189_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 7 v) = true := by decide +kernel
theorem col189 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 189) 189 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col189_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col189_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s189_2_0
    · exact s189_2_1
    · exact s189_2_2
    · exact s189_2_3
    · exact s189_2_4
    · exact s189_2_5
    · exact s189_2_6
    · exact s189_2_7
  · fin_cases v
    · exact s189_3_0
    · exact s189_3_1
    · exact s189_3_2
    · exact s189_3_3
    · exact s189_3_4
    · exact s189_3_5
    · exact s189_3_6
    · exact s189_3_7
  · fin_cases v
    · exact s189_4_0
    · exact s189_4_1
    · exact s189_4_2
    · exact s189_4_3
    · exact s189_4_4
    · exact s189_4_5
    · exact s189_4_6
    · exact s189_4_7
  · fin_cases v
    · exact s189_5_0
    · exact s189_5_1
    · exact s189_5_2
    · exact s189_5_3
    · exact s189_5_4
    · exact s189_5_5
    · exact s189_5_6
    · exact s189_5_7
  · exact List.all_eq_true.mp col189_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col189_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
