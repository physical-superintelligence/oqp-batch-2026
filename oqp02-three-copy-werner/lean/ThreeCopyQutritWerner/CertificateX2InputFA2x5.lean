module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [25, 30). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col25_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 0 v) = true := by decide +kernel
theorem col25_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 1 v) = true := by decide +kernel
theorem s25_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 0 = true := by decide +kernel
theorem s25_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 1 = true := by decide +kernel
theorem s25_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 2 = true := by decide +kernel
theorem s25_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 3 = true := by decide +kernel
theorem k25_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k25_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k25_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s25_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k25_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k25_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TTsaaD 2 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k25_2_4_80 k h.1 (by omega)
theorem s25_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 5 = true := by decide +kernel
theorem s25_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 6 = true := by decide +kernel
theorem s25_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 2 7 = true := by decide +kernel
theorem s25_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 0 = true := by decide +kernel
theorem s25_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 1 = true := by decide +kernel
theorem s25_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 2 = true := by decide +kernel
theorem s25_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 3 = true := by decide +kernel
theorem k25_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k25_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k25_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s25_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k25_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k25_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 3 4).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k25_3_4_80 k h.1 (by omega)
theorem s25_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 5 = true := by decide +kernel
theorem s25_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 6 = true := by decide +kernel
theorem s25_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 3 7 = true := by decide +kernel
theorem s25_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 0 = true := by decide +kernel
theorem s25_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 1 = true := by decide +kernel
theorem s25_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 2 = true := by decide +kernel
theorem s25_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 3 = true := by decide +kernel
theorem s25_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 4 = true := by decide +kernel
theorem k25_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k25_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k25_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k25_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k25_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k25_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k25_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k25_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k25_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s25_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k25_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k25_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k25_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k25_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k25_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k25_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k25_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k25_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 5).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k25_4_5_40 k h.1 (by omega)
theorem k25_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k25_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k25_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k25_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k25_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k25_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k25_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k25_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k25_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k25_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k25_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s25_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k25_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k25_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k25_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k25_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k25_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k25_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k25_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k25_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k25_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k25_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 4 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k25_4_6_50 k h.1 (by omega)
theorem s25_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 4 7 = true := by decide +kernel
theorem s25_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 0 = true := by decide +kernel
theorem s25_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 1 = true := by decide +kernel
theorem s25_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 2 = true := by decide +kernel
theorem s25_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 3 = true := by decide +kernel
theorem s25_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 4 = true := by decide +kernel
theorem s25_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 5 = true := by decide +kernel
theorem k25_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k25_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k25_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k25_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k25_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k25_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s25_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k25_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k25_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k25_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k25_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k25_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 25) ((InDA2.TCasaD 3 5 6).getD (25 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k25_5_6_50 k h.1 (by omega)
theorem s25_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 5 7 = true := by decide +kernel
theorem col25_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 6 v) = true := by decide +kernel
theorem col25_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 7 v) = true := by decide +kernel
theorem col25 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 25) 25 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col25_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col25_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s25_2_0
    · exact s25_2_1
    · exact s25_2_2
    · exact s25_2_3
    · exact s25_2_4
    · exact s25_2_5
    · exact s25_2_6
    · exact s25_2_7
  · fin_cases v
    · exact s25_3_0
    · exact s25_3_1
    · exact s25_3_2
    · exact s25_3_3
    · exact s25_3_4
    · exact s25_3_5
    · exact s25_3_6
    · exact s25_3_7
  · fin_cases v
    · exact s25_4_0
    · exact s25_4_1
    · exact s25_4_2
    · exact s25_4_3
    · exact s25_4_4
    · exact s25_4_5
    · exact s25_4_6
    · exact s25_4_7
  · fin_cases v
    · exact s25_5_0
    · exact s25_5_1
    · exact s25_5_2
    · exact s25_5_3
    · exact s25_5_4
    · exact s25_5_5
    · exact s25_5_6
    · exact s25_5_7
  · exact List.all_eq_true.mp col25_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col25_7 v (List.mem_finRange v)
theorem col26_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 0 v) = true := by decide +kernel
theorem col26_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 1 v) = true := by decide +kernel
theorem s26_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 0 = true := by decide +kernel
theorem s26_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 1 = true := by decide +kernel
theorem s26_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 2 = true := by decide +kernel
theorem s26_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 3 = true := by decide +kernel
theorem k26_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k26_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k26_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s26_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k26_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k26_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k26_2_4_80 k h.1 (by omega)
theorem s26_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 5 = true := by decide +kernel
theorem s26_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 6 = true := by decide +kernel
theorem s26_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 2 7 = true := by decide +kernel
theorem s26_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 0 = true := by decide +kernel
theorem s26_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 1 = true := by decide +kernel
theorem s26_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 2 = true := by decide +kernel
theorem s26_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 3 = true := by decide +kernel
theorem k26_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k26_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k26_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s26_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k26_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k26_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 26) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (26 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k26_3_4_80 k h.1 (by omega)
theorem s26_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 5 = true := by decide +kernel
theorem s26_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 6 = true := by decide +kernel
theorem s26_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 3 7 = true := by decide +kernel
theorem s26_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 0 = true := by decide +kernel
theorem s26_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 1 = true := by decide +kernel
theorem s26_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 2 = true := by decide +kernel
theorem s26_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 3 = true := by decide +kernel
theorem s26_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 4 = true := by decide +kernel
theorem k26_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k26_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k26_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k26_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k26_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k26_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k26_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k26_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k26_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s26_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k26_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k26_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k26_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k26_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k26_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k26_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k26_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k26_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 5).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k26_4_5_40 k h.1 (by omega)
theorem k26_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k26_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k26_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k26_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k26_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k26_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k26_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k26_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k26_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k26_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k26_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s26_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k26_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k26_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k26_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k26_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k26_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k26_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k26_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k26_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k26_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k26_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 4 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k26_4_6_50 k h.1 (by omega)
theorem s26_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 4 7 = true := by decide +kernel
theorem s26_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 0 = true := by decide +kernel
theorem s26_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 1 = true := by decide +kernel
theorem s26_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 2 = true := by decide +kernel
theorem s26_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 3 = true := by decide +kernel
theorem s26_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 4 = true := by decide +kernel
theorem s26_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 5 = true := by decide +kernel
theorem k26_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k26_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k26_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k26_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k26_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k26_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s26_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k26_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k26_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k26_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k26_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k26_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 26) ((InDA2.TCasaD 4 5 6).getD (26 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k26_5_6_50 k h.1 (by omega)
theorem s26_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 5 7 = true := by decide +kernel
theorem col26_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 6 v) = true := by decide +kernel
theorem col26_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 7 v) = true := by decide +kernel
theorem col26 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 26) 26 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col26_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col26_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s26_2_0
    · exact s26_2_1
    · exact s26_2_2
    · exact s26_2_3
    · exact s26_2_4
    · exact s26_2_5
    · exact s26_2_6
    · exact s26_2_7
  · fin_cases v
    · exact s26_3_0
    · exact s26_3_1
    · exact s26_3_2
    · exact s26_3_3
    · exact s26_3_4
    · exact s26_3_5
    · exact s26_3_6
    · exact s26_3_7
  · fin_cases v
    · exact s26_4_0
    · exact s26_4_1
    · exact s26_4_2
    · exact s26_4_3
    · exact s26_4_4
    · exact s26_4_5
    · exact s26_4_6
    · exact s26_4_7
  · fin_cases v
    · exact s26_5_0
    · exact s26_5_1
    · exact s26_5_2
    · exact s26_5_3
    · exact s26_5_4
    · exact s26_5_5
    · exact s26_5_6
    · exact s26_5_7
  · exact List.all_eq_true.mp col26_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col26_7 v (List.mem_finRange v)
theorem col27_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 0 v) = true := by decide +kernel
theorem col27_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 1 v) = true := by decide +kernel
theorem s27_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 0 = true := by decide +kernel
theorem s27_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 1 = true := by decide +kernel
theorem s27_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 2 = true := by decide +kernel
theorem s27_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 3 = true := by decide +kernel
theorem k27_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k27_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k27_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s27_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k27_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k27_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k27_2_4_80 k h.1 (by omega)
theorem s27_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 5 = true := by decide +kernel
theorem s27_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 6 = true := by decide +kernel
theorem s27_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 2 7 = true := by decide +kernel
theorem s27_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 0 = true := by decide +kernel
theorem s27_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 1 = true := by decide +kernel
theorem s27_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 2 = true := by decide +kernel
theorem s27_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 3 = true := by decide +kernel
theorem k27_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k27_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k27_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s27_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k27_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k27_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 27) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (27 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k27_3_4_80 k h.1 (by omega)
theorem s27_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 5 = true := by decide +kernel
theorem s27_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 6 = true := by decide +kernel
theorem s27_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 3 7 = true := by decide +kernel
theorem s27_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 0 = true := by decide +kernel
theorem s27_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 1 = true := by decide +kernel
theorem s27_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 2 = true := by decide +kernel
theorem s27_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 3 = true := by decide +kernel
theorem s27_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 4 = true := by decide +kernel
theorem k27_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k27_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k27_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k27_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k27_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k27_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k27_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k27_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k27_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s27_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k27_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k27_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k27_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k27_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k27_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k27_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k27_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k27_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 5).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k27_4_5_40 k h.1 (by omega)
theorem k27_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k27_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k27_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k27_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k27_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k27_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k27_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k27_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k27_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k27_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k27_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s27_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k27_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k27_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k27_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k27_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k27_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k27_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k27_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k27_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k27_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k27_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 4 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k27_4_6_50 k h.1 (by omega)
theorem s27_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 4 7 = true := by decide +kernel
theorem s27_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 0 = true := by decide +kernel
theorem s27_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 1 = true := by decide +kernel
theorem s27_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 2 = true := by decide +kernel
theorem s27_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 3 = true := by decide +kernel
theorem s27_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 4 = true := by decide +kernel
theorem s27_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 5 = true := by decide +kernel
theorem k27_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k27_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k27_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k27_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k27_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k27_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s27_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k27_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k27_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k27_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k27_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k27_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 27) ((InDA2.TCasaD 4 5 6).getD (27 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k27_5_6_50 k h.1 (by omega)
theorem s27_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 5 7 = true := by decide +kernel
theorem col27_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 6 v) = true := by decide +kernel
theorem col27_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 7 v) = true := by decide +kernel
theorem col27 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 27) 27 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col27_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col27_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s27_2_0
    · exact s27_2_1
    · exact s27_2_2
    · exact s27_2_3
    · exact s27_2_4
    · exact s27_2_5
    · exact s27_2_6
    · exact s27_2_7
  · fin_cases v
    · exact s27_3_0
    · exact s27_3_1
    · exact s27_3_2
    · exact s27_3_3
    · exact s27_3_4
    · exact s27_3_5
    · exact s27_3_6
    · exact s27_3_7
  · fin_cases v
    · exact s27_4_0
    · exact s27_4_1
    · exact s27_4_2
    · exact s27_4_3
    · exact s27_4_4
    · exact s27_4_5
    · exact s27_4_6
    · exact s27_4_7
  · fin_cases v
    · exact s27_5_0
    · exact s27_5_1
    · exact s27_5_2
    · exact s27_5_3
    · exact s27_5_4
    · exact s27_5_5
    · exact s27_5_6
    · exact s27_5_7
  · exact List.all_eq_true.mp col27_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col27_7 v (List.mem_finRange v)
theorem col28_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 0 v) = true := by decide +kernel
theorem col28_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 1 v) = true := by decide +kernel
theorem s28_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 0 = true := by decide +kernel
theorem s28_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 1 = true := by decide +kernel
theorem s28_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 2 = true := by decide +kernel
theorem s28_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 3 = true := by decide +kernel
theorem k28_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k28_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k28_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s28_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k28_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k28_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k28_2_4_80 k h.1 (by omega)
theorem s28_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 5 = true := by decide +kernel
theorem s28_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 6 = true := by decide +kernel
theorem s28_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 2 7 = true := by decide +kernel
theorem s28_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 0 = true := by decide +kernel
theorem s28_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 1 = true := by decide +kernel
theorem s28_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 2 = true := by decide +kernel
theorem s28_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 3 = true := by decide +kernel
theorem k28_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k28_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k28_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s28_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k28_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k28_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 28) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (28 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k28_3_4_80 k h.1 (by omega)
theorem s28_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 5 = true := by decide +kernel
theorem s28_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 6 = true := by decide +kernel
theorem s28_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 3 7 = true := by decide +kernel
theorem s28_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 0 = true := by decide +kernel
theorem s28_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 1 = true := by decide +kernel
theorem s28_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 2 = true := by decide +kernel
theorem s28_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 3 = true := by decide +kernel
theorem s28_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 4 = true := by decide +kernel
theorem k28_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k28_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k28_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k28_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k28_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k28_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k28_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k28_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k28_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s28_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k28_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k28_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k28_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k28_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k28_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k28_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k28_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k28_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 5).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k28_4_5_40 k h.1 (by omega)
theorem k28_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k28_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k28_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k28_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k28_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k28_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k28_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k28_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k28_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k28_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k28_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s28_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k28_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k28_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k28_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k28_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k28_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k28_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k28_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k28_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k28_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k28_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 4 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k28_4_6_50 k h.1 (by omega)
theorem s28_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 4 7 = true := by decide +kernel
theorem s28_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 0 = true := by decide +kernel
theorem s28_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 1 = true := by decide +kernel
theorem s28_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 2 = true := by decide +kernel
theorem s28_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 3 = true := by decide +kernel
theorem s28_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 4 = true := by decide +kernel
theorem s28_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 5 = true := by decide +kernel
theorem k28_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k28_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k28_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k28_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k28_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k28_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s28_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k28_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k28_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k28_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k28_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k28_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 28) ((InDA2.TCasaD 4 5 6).getD (28 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k28_5_6_50 k h.1 (by omega)
theorem s28_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 5 7 = true := by decide +kernel
theorem col28_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 6 v) = true := by decide +kernel
theorem col28_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 7 v) = true := by decide +kernel
theorem col28 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 28) 28 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col28_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col28_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s28_2_0
    · exact s28_2_1
    · exact s28_2_2
    · exact s28_2_3
    · exact s28_2_4
    · exact s28_2_5
    · exact s28_2_6
    · exact s28_2_7
  · fin_cases v
    · exact s28_3_0
    · exact s28_3_1
    · exact s28_3_2
    · exact s28_3_3
    · exact s28_3_4
    · exact s28_3_5
    · exact s28_3_6
    · exact s28_3_7
  · fin_cases v
    · exact s28_4_0
    · exact s28_4_1
    · exact s28_4_2
    · exact s28_4_3
    · exact s28_4_4
    · exact s28_4_5
    · exact s28_4_6
    · exact s28_4_7
  · fin_cases v
    · exact s28_5_0
    · exact s28_5_1
    · exact s28_5_2
    · exact s28_5_3
    · exact s28_5_4
    · exact s28_5_5
    · exact s28_5_6
    · exact s28_5_7
  · exact List.all_eq_true.mp col28_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col28_7 v (List.mem_finRange v)
theorem col29_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 0 v) = true := by decide +kernel
theorem col29_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 1 v) = true := by decide +kernel
theorem s29_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 0 = true := by decide +kernel
theorem s29_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 1 = true := by decide +kernel
theorem s29_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 2 = true := by decide +kernel
theorem s29_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 3 = true := by decide +kernel
theorem k29_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k29_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k29_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s29_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k29_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k29_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k29_2_4_80 k h.1 (by omega)
theorem s29_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 5 = true := by decide +kernel
theorem s29_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 6 = true := by decide +kernel
theorem s29_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 2 7 = true := by decide +kernel
theorem s29_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 0 = true := by decide +kernel
theorem s29_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 1 = true := by decide +kernel
theorem s29_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 2 = true := by decide +kernel
theorem s29_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 3 = true := by decide +kernel
theorem k29_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k29_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k29_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s29_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k29_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k29_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 29) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (29 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k29_3_4_80 k h.1 (by omega)
theorem s29_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 5 = true := by decide +kernel
theorem s29_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 6 = true := by decide +kernel
theorem s29_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 3 7 = true := by decide +kernel
theorem s29_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 0 = true := by decide +kernel
theorem s29_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 1 = true := by decide +kernel
theorem s29_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 2 = true := by decide +kernel
theorem s29_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 3 = true := by decide +kernel
theorem s29_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 4 = true := by decide +kernel
theorem k29_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k29_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k29_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k29_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k29_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k29_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k29_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k29_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k29_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s29_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k29_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k29_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k29_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k29_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k29_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k29_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k29_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k29_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 5).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k29_4_5_40 k h.1 (by omega)
theorem k29_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k29_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k29_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k29_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k29_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k29_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k29_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k29_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k29_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k29_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k29_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s29_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k29_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k29_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k29_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k29_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k29_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k29_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k29_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k29_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k29_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k29_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 4 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k29_4_6_50 k h.1 (by omega)
theorem s29_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 4 7 = true := by decide +kernel
theorem s29_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 0 = true := by decide +kernel
theorem s29_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 1 = true := by decide +kernel
theorem s29_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 2 = true := by decide +kernel
theorem s29_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 3 = true := by decide +kernel
theorem s29_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 4 = true := by decide +kernel
theorem s29_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 5 = true := by decide +kernel
theorem k29_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k29_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k29_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k29_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k29_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k29_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s29_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k29_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k29_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k29_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k29_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k29_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 29) ((InDA2.TCasaD 4 5 6).getD (29 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k29_5_6_50 k h.1 (by omega)
theorem s29_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 5 7 = true := by decide +kernel
theorem col29_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 6 v) = true := by decide +kernel
theorem col29_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 7 v) = true := by decide +kernel
theorem col29 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 29) 29 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col29_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col29_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s29_2_0
    · exact s29_2_1
    · exact s29_2_2
    · exact s29_2_3
    · exact s29_2_4
    · exact s29_2_5
    · exact s29_2_6
    · exact s29_2_7
  · fin_cases v
    · exact s29_3_0
    · exact s29_3_1
    · exact s29_3_2
    · exact s29_3_3
    · exact s29_3_4
    · exact s29_3_5
    · exact s29_3_6
    · exact s29_3_7
  · fin_cases v
    · exact s29_4_0
    · exact s29_4_1
    · exact s29_4_2
    · exact s29_4_3
    · exact s29_4_4
    · exact s29_4_5
    · exact s29_4_6
    · exact s29_4_7
  · fin_cases v
    · exact s29_5_0
    · exact s29_5_1
    · exact s29_5_2
    · exact s29_5_3
    · exact s29_5_4
    · exact s29_5_5
    · exact s29_5_6
    · exact s29_5_7
  · exact List.all_eq_true.mp col29_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col29_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
