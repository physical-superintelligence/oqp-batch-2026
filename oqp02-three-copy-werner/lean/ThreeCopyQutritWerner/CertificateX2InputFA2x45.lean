module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [225, 230). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col225_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 0 v) = true := by decide +kernel
theorem col225_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 1 v) = true := by decide +kernel
theorem s225_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 0 = true := by decide +kernel
theorem s225_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 1 = true := by decide +kernel
theorem s225_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 2 = true := by decide +kernel
theorem s225_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 3 = true := by decide +kernel
theorem k225_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k225_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k225_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s225_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k225_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k225_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k225_2_4_80 k h.1 (by omega)
theorem s225_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 5 = true := by decide +kernel
theorem s225_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 6 = true := by decide +kernel
theorem s225_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 2 7 = true := by decide +kernel
theorem s225_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 0 = true := by decide +kernel
theorem s225_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 1 = true := by decide +kernel
theorem s225_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 2 = true := by decide +kernel
theorem s225_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 3 = true := by decide +kernel
theorem k225_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k225_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k225_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s225_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k225_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k225_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k225_3_4_80 k h.1 (by omega)
theorem s225_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 5 = true := by decide +kernel
theorem s225_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 6 = true := by decide +kernel
theorem s225_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 3 7 = true := by decide +kernel
theorem s225_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 0 = true := by decide +kernel
theorem s225_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 1 = true := by decide +kernel
theorem s225_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 2 = true := by decide +kernel
theorem s225_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 3 = true := by decide +kernel
theorem k225_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k225_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k225_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k225_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k225_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k225_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k225_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k225_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k225_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k225_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k225_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k225_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k225_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k225_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k225_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k225_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k225_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k225_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k225_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k225_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k225_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s225_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k225_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k225_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k225_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k225_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k225_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k225_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k225_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k225_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k225_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k225_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k225_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k225_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k225_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k225_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k225_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k225_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k225_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k225_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k225_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k225_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k225_4_4_100 k h.1 (by omega)
theorem k225_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k225_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k225_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k225_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k225_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k225_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k225_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k225_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k225_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s225_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k225_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k225_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k225_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k225_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k225_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k225_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k225_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k225_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k225_4_5_40 k h.1 (by omega)
theorem k225_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k225_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k225_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k225_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k225_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k225_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k225_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k225_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k225_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k225_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k225_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s225_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k225_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k225_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k225_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k225_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k225_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k225_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k225_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k225_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k225_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k225_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k225_4_6_50 k h.1 (by omega)
theorem s225_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 4 7 = true := by decide +kernel
theorem s225_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 0 = true := by decide +kernel
theorem s225_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 1 = true := by decide +kernel
theorem s225_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 2 = true := by decide +kernel
theorem s225_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 3 = true := by decide +kernel
theorem k225_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k225_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k225_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k225_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k225_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k225_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k225_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k225_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k225_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k225_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k225_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s225_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k225_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k225_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k225_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k225_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k225_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k225_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k225_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k225_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k225_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k225_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k225_5_4_100 k h.1 (by omega)
theorem k225_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k225_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k225_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k225_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k225_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s225_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k225_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k225_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k225_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k225_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k225_5_5_40 k h.1 (by omega)
theorem k225_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k225_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k225_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k225_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k225_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k225_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s225_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k225_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k225_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k225_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k225_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k225_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 225) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (225 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k225_5_6_50 k h.1 (by omega)
theorem s225_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 5 7 = true := by decide +kernel
theorem col225_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 6 v) = true := by decide +kernel
theorem col225_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 7 v) = true := by decide +kernel
theorem col225 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 225) 225 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col225_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col225_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s225_2_0
    · exact s225_2_1
    · exact s225_2_2
    · exact s225_2_3
    · exact s225_2_4
    · exact s225_2_5
    · exact s225_2_6
    · exact s225_2_7
  · fin_cases v
    · exact s225_3_0
    · exact s225_3_1
    · exact s225_3_2
    · exact s225_3_3
    · exact s225_3_4
    · exact s225_3_5
    · exact s225_3_6
    · exact s225_3_7
  · fin_cases v
    · exact s225_4_0
    · exact s225_4_1
    · exact s225_4_2
    · exact s225_4_3
    · exact s225_4_4
    · exact s225_4_5
    · exact s225_4_6
    · exact s225_4_7
  · fin_cases v
    · exact s225_5_0
    · exact s225_5_1
    · exact s225_5_2
    · exact s225_5_3
    · exact s225_5_4
    · exact s225_5_5
    · exact s225_5_6
    · exact s225_5_7
  · exact List.all_eq_true.mp col225_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col225_7 v (List.mem_finRange v)
theorem col226_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 0 v) = true := by decide +kernel
theorem col226_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 1 v) = true := by decide +kernel
theorem s226_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 0 = true := by decide +kernel
theorem s226_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 1 = true := by decide +kernel
theorem s226_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 2 = true := by decide +kernel
theorem s226_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 3 = true := by decide +kernel
theorem k226_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k226_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k226_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s226_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k226_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k226_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k226_2_4_80 k h.1 (by omega)
theorem s226_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 5 = true := by decide +kernel
theorem s226_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 6 = true := by decide +kernel
theorem s226_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 2 7 = true := by decide +kernel
theorem s226_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 0 = true := by decide +kernel
theorem s226_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 1 = true := by decide +kernel
theorem s226_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 2 = true := by decide +kernel
theorem s226_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 3 = true := by decide +kernel
theorem k226_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k226_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k226_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s226_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k226_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k226_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k226_3_4_80 k h.1 (by omega)
theorem s226_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 5 = true := by decide +kernel
theorem s226_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 6 = true := by decide +kernel
theorem s226_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 3 7 = true := by decide +kernel
theorem s226_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 0 = true := by decide +kernel
theorem s226_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 1 = true := by decide +kernel
theorem s226_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 2 = true := by decide +kernel
theorem s226_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 3 = true := by decide +kernel
theorem k226_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k226_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k226_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k226_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k226_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k226_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k226_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k226_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k226_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k226_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k226_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k226_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k226_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k226_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k226_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k226_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k226_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k226_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k226_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k226_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k226_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s226_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k226_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k226_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k226_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k226_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k226_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k226_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k226_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k226_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k226_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k226_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k226_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k226_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k226_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k226_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k226_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k226_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k226_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k226_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k226_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k226_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k226_4_4_100 k h.1 (by omega)
theorem k226_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k226_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k226_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k226_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k226_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k226_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k226_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k226_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k226_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s226_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k226_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k226_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k226_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k226_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k226_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k226_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k226_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k226_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k226_4_5_40 k h.1 (by omega)
theorem k226_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k226_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k226_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k226_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k226_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k226_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k226_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k226_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k226_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k226_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k226_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s226_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k226_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k226_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k226_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k226_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k226_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k226_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k226_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k226_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k226_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k226_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k226_4_6_50 k h.1 (by omega)
theorem s226_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 4 7 = true := by decide +kernel
theorem s226_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 0 = true := by decide +kernel
theorem s226_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 1 = true := by decide +kernel
theorem s226_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 2 = true := by decide +kernel
theorem s226_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 3 = true := by decide +kernel
theorem k226_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k226_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k226_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k226_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k226_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k226_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k226_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k226_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k226_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k226_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k226_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s226_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k226_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k226_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k226_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k226_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k226_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k226_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k226_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k226_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k226_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k226_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k226_5_4_100 k h.1 (by omega)
theorem k226_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k226_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k226_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k226_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k226_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s226_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k226_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k226_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k226_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k226_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k226_5_5_40 k h.1 (by omega)
theorem k226_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k226_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k226_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k226_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k226_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k226_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s226_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k226_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k226_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k226_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k226_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k226_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 226) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (226 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k226_5_6_50 k h.1 (by omega)
theorem s226_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 5 7 = true := by decide +kernel
theorem col226_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 6 v) = true := by decide +kernel
theorem col226_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 7 v) = true := by decide +kernel
theorem col226 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 226) 226 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col226_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col226_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s226_2_0
    · exact s226_2_1
    · exact s226_2_2
    · exact s226_2_3
    · exact s226_2_4
    · exact s226_2_5
    · exact s226_2_6
    · exact s226_2_7
  · fin_cases v
    · exact s226_3_0
    · exact s226_3_1
    · exact s226_3_2
    · exact s226_3_3
    · exact s226_3_4
    · exact s226_3_5
    · exact s226_3_6
    · exact s226_3_7
  · fin_cases v
    · exact s226_4_0
    · exact s226_4_1
    · exact s226_4_2
    · exact s226_4_3
    · exact s226_4_4
    · exact s226_4_5
    · exact s226_4_6
    · exact s226_4_7
  · fin_cases v
    · exact s226_5_0
    · exact s226_5_1
    · exact s226_5_2
    · exact s226_5_3
    · exact s226_5_4
    · exact s226_5_5
    · exact s226_5_6
    · exact s226_5_7
  · exact List.all_eq_true.mp col226_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col226_7 v (List.mem_finRange v)
theorem col227_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 0 v) = true := by decide +kernel
theorem col227_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 1 v) = true := by decide +kernel
theorem s227_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 0 = true := by decide +kernel
theorem s227_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 1 = true := by decide +kernel
theorem s227_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 2 = true := by decide +kernel
theorem s227_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 3 = true := by decide +kernel
theorem k227_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k227_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k227_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s227_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k227_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k227_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k227_2_4_80 k h.1 (by omega)
theorem s227_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 5 = true := by decide +kernel
theorem s227_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 6 = true := by decide +kernel
theorem s227_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 2 7 = true := by decide +kernel
theorem s227_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 0 = true := by decide +kernel
theorem s227_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 1 = true := by decide +kernel
theorem s227_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 2 = true := by decide +kernel
theorem s227_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 3 = true := by decide +kernel
theorem k227_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k227_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k227_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s227_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k227_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k227_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k227_3_4_80 k h.1 (by omega)
theorem s227_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 5 = true := by decide +kernel
theorem s227_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 6 = true := by decide +kernel
theorem s227_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 3 7 = true := by decide +kernel
theorem s227_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 0 = true := by decide +kernel
theorem s227_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 1 = true := by decide +kernel
theorem s227_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 2 = true := by decide +kernel
theorem s227_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 3 = true := by decide +kernel
theorem k227_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k227_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k227_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k227_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k227_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k227_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k227_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k227_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k227_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k227_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k227_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k227_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k227_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k227_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k227_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k227_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k227_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k227_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k227_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k227_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k227_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s227_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k227_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k227_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k227_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k227_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k227_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k227_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k227_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k227_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k227_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k227_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k227_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k227_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k227_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k227_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k227_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k227_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k227_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k227_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k227_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k227_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k227_4_4_100 k h.1 (by omega)
theorem k227_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k227_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k227_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k227_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k227_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k227_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k227_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k227_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k227_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s227_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k227_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k227_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k227_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k227_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k227_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k227_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k227_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k227_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k227_4_5_40 k h.1 (by omega)
theorem k227_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k227_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k227_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k227_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k227_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k227_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k227_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k227_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k227_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k227_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k227_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s227_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k227_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k227_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k227_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k227_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k227_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k227_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k227_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k227_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k227_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k227_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k227_4_6_50 k h.1 (by omega)
theorem s227_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 4 7 = true := by decide +kernel
theorem s227_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 0 = true := by decide +kernel
theorem s227_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 1 = true := by decide +kernel
theorem s227_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 2 = true := by decide +kernel
theorem s227_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 3 = true := by decide +kernel
theorem k227_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k227_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k227_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k227_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k227_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k227_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k227_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k227_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k227_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k227_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k227_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s227_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k227_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k227_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k227_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k227_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k227_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k227_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k227_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k227_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k227_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k227_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k227_5_4_100 k h.1 (by omega)
theorem k227_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k227_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k227_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k227_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k227_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s227_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k227_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k227_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k227_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k227_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k227_5_5_40 k h.1 (by omega)
theorem k227_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k227_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k227_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k227_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k227_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k227_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s227_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k227_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k227_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k227_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k227_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k227_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 227) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (227 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k227_5_6_50 k h.1 (by omega)
theorem s227_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 5 7 = true := by decide +kernel
theorem col227_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 6 v) = true := by decide +kernel
theorem col227_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 7 v) = true := by decide +kernel
theorem col227 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 227) 227 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col227_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col227_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s227_2_0
    · exact s227_2_1
    · exact s227_2_2
    · exact s227_2_3
    · exact s227_2_4
    · exact s227_2_5
    · exact s227_2_6
    · exact s227_2_7
  · fin_cases v
    · exact s227_3_0
    · exact s227_3_1
    · exact s227_3_2
    · exact s227_3_3
    · exact s227_3_4
    · exact s227_3_5
    · exact s227_3_6
    · exact s227_3_7
  · fin_cases v
    · exact s227_4_0
    · exact s227_4_1
    · exact s227_4_2
    · exact s227_4_3
    · exact s227_4_4
    · exact s227_4_5
    · exact s227_4_6
    · exact s227_4_7
  · fin_cases v
    · exact s227_5_0
    · exact s227_5_1
    · exact s227_5_2
    · exact s227_5_3
    · exact s227_5_4
    · exact s227_5_5
    · exact s227_5_6
    · exact s227_5_7
  · exact List.all_eq_true.mp col227_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col227_7 v (List.mem_finRange v)
theorem col228_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 0 v) = true := by decide +kernel
theorem col228_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 1 v) = true := by decide +kernel
theorem s228_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 0 = true := by decide +kernel
theorem s228_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 1 = true := by decide +kernel
theorem s228_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 2 = true := by decide +kernel
theorem s228_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 3 = true := by decide +kernel
theorem k228_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k228_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k228_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s228_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k228_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k228_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k228_2_4_80 k h.1 (by omega)
theorem s228_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 5 = true := by decide +kernel
theorem s228_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 6 = true := by decide +kernel
theorem s228_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 2 7 = true := by decide +kernel
theorem s228_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 0 = true := by decide +kernel
theorem s228_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 1 = true := by decide +kernel
theorem s228_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 2 = true := by decide +kernel
theorem s228_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 3 = true := by decide +kernel
theorem k228_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k228_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k228_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s228_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k228_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k228_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k228_3_4_80 k h.1 (by omega)
theorem s228_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 5 = true := by decide +kernel
theorem s228_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 6 = true := by decide +kernel
theorem s228_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 3 7 = true := by decide +kernel
theorem s228_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 0 = true := by decide +kernel
theorem s228_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 1 = true := by decide +kernel
theorem s228_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 2 = true := by decide +kernel
theorem s228_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 3 = true := by decide +kernel
theorem k228_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k228_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k228_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k228_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k228_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k228_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k228_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k228_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k228_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k228_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k228_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k228_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k228_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k228_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k228_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k228_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k228_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k228_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k228_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k228_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k228_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s228_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k228_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k228_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k228_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k228_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k228_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k228_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k228_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k228_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k228_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k228_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k228_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k228_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k228_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k228_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k228_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k228_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k228_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k228_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k228_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k228_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k228_4_4_100 k h.1 (by omega)
theorem k228_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k228_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k228_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k228_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k228_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k228_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k228_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k228_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k228_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s228_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k228_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k228_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k228_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k228_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k228_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k228_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k228_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k228_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k228_4_5_40 k h.1 (by omega)
theorem k228_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k228_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k228_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k228_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k228_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k228_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k228_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k228_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k228_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k228_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k228_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s228_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k228_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k228_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k228_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k228_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k228_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k228_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k228_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k228_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k228_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k228_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k228_4_6_50 k h.1 (by omega)
theorem s228_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 4 7 = true := by decide +kernel
theorem s228_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 0 = true := by decide +kernel
theorem s228_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 1 = true := by decide +kernel
theorem s228_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 2 = true := by decide +kernel
theorem s228_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 3 = true := by decide +kernel
theorem k228_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k228_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k228_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k228_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k228_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k228_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k228_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k228_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k228_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k228_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k228_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s228_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k228_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k228_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k228_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k228_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k228_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k228_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k228_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k228_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k228_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k228_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k228_5_4_100 k h.1 (by omega)
theorem k228_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k228_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k228_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k228_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k228_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s228_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k228_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k228_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k228_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k228_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k228_5_5_40 k h.1 (by omega)
theorem k228_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k228_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k228_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k228_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k228_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k228_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s228_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k228_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k228_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k228_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k228_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k228_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 228) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (228 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k228_5_6_50 k h.1 (by omega)
theorem s228_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 5 7 = true := by decide +kernel
theorem col228_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 6 v) = true := by decide +kernel
theorem col228_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 7 v) = true := by decide +kernel
theorem col228 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 228) 228 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col228_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col228_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s228_2_0
    · exact s228_2_1
    · exact s228_2_2
    · exact s228_2_3
    · exact s228_2_4
    · exact s228_2_5
    · exact s228_2_6
    · exact s228_2_7
  · fin_cases v
    · exact s228_3_0
    · exact s228_3_1
    · exact s228_3_2
    · exact s228_3_3
    · exact s228_3_4
    · exact s228_3_5
    · exact s228_3_6
    · exact s228_3_7
  · fin_cases v
    · exact s228_4_0
    · exact s228_4_1
    · exact s228_4_2
    · exact s228_4_3
    · exact s228_4_4
    · exact s228_4_5
    · exact s228_4_6
    · exact s228_4_7
  · fin_cases v
    · exact s228_5_0
    · exact s228_5_1
    · exact s228_5_2
    · exact s228_5_3
    · exact s228_5_4
    · exact s228_5_5
    · exact s228_5_6
    · exact s228_5_7
  · exact List.all_eq_true.mp col228_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col228_7 v (List.mem_finRange v)
theorem col229_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 0 v) = true := by decide +kernel
theorem col229_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 1 v) = true := by decide +kernel
theorem s229_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 0 = true := by decide +kernel
theorem s229_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 1 = true := by decide +kernel
theorem s229_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 2 = true := by decide +kernel
theorem s229_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 3 = true := by decide +kernel
theorem k229_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k229_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k229_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s229_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k229_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k229_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k229_2_4_80 k h.1 (by omega)
theorem s229_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 5 = true := by decide +kernel
theorem s229_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 6 = true := by decide +kernel
theorem s229_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 2 7 = true := by decide +kernel
theorem s229_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 0 = true := by decide +kernel
theorem s229_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 1 = true := by decide +kernel
theorem s229_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 2 = true := by decide +kernel
theorem s229_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 3 = true := by decide +kernel
theorem k229_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k229_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k229_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s229_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k229_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k229_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k229_3_4_80 k h.1 (by omega)
theorem s229_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 5 = true := by decide +kernel
theorem s229_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 6 = true := by decide +kernel
theorem s229_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 3 7 = true := by decide +kernel
theorem s229_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 0 = true := by decide +kernel
theorem s229_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 1 = true := by decide +kernel
theorem s229_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 2 = true := by decide +kernel
theorem s229_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 3 = true := by decide +kernel
theorem k229_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k229_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k229_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k229_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k229_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k229_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k229_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k229_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k229_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k229_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k229_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k229_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k229_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k229_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k229_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k229_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k229_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k229_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k229_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k229_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k229_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s229_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k229_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k229_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k229_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k229_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k229_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k229_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k229_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k229_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k229_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k229_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k229_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k229_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k229_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k229_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k229_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k229_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k229_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k229_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k229_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k229_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k229_4_4_100 k h.1 (by omega)
theorem k229_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k229_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k229_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k229_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k229_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k229_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k229_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k229_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k229_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s229_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k229_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k229_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k229_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k229_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k229_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k229_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k229_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k229_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k229_4_5_40 k h.1 (by omega)
theorem k229_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k229_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k229_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k229_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k229_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k229_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k229_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k229_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k229_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k229_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k229_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s229_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k229_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k229_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k229_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k229_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k229_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k229_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k229_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k229_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k229_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k229_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k229_4_6_50 k h.1 (by omega)
theorem s229_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 4 7 = true := by decide +kernel
theorem s229_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 0 = true := by decide +kernel
theorem s229_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 1 = true := by decide +kernel
theorem s229_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 2 = true := by decide +kernel
theorem s229_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 3 = true := by decide +kernel
theorem k229_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k229_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k229_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k229_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k229_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k229_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k229_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k229_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k229_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k229_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k229_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s229_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k229_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k229_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k229_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k229_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k229_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k229_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k229_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k229_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k229_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k229_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k229_5_4_100 k h.1 (by omega)
theorem k229_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k229_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k229_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k229_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k229_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s229_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k229_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k229_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k229_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k229_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k229_5_5_40 k h.1 (by omega)
theorem k229_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k229_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k229_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k229_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k229_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k229_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s229_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k229_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k229_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k229_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k229_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k229_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 229) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (229 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k229_5_6_50 k h.1 (by omega)
theorem s229_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 5 7 = true := by decide +kernel
theorem col229_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 6 v) = true := by decide +kernel
theorem col229_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 7 v) = true := by decide +kernel
theorem col229 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 229) 229 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col229_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col229_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s229_2_0
    · exact s229_2_1
    · exact s229_2_2
    · exact s229_2_3
    · exact s229_2_4
    · exact s229_2_5
    · exact s229_2_6
    · exact s229_2_7
  · fin_cases v
    · exact s229_3_0
    · exact s229_3_1
    · exact s229_3_2
    · exact s229_3_3
    · exact s229_3_4
    · exact s229_3_5
    · exact s229_3_6
    · exact s229_3_7
  · fin_cases v
    · exact s229_4_0
    · exact s229_4_1
    · exact s229_4_2
    · exact s229_4_3
    · exact s229_4_4
    · exact s229_4_5
    · exact s229_4_6
    · exact s229_4_7
  · fin_cases v
    · exact s229_5_0
    · exact s229_5_1
    · exact s229_5_2
    · exact s229_5_3
    · exact s229_5_4
    · exact s229_5_5
    · exact s229_5_6
    · exact s229_5_7
  · exact List.all_eq_true.mp col229_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col229_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
