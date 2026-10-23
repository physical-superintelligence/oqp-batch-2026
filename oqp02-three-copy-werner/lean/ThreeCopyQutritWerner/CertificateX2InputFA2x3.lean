module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [15, 20). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col15_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 0 v) = true := by decide +kernel
theorem col15_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 1 v) = true := by decide +kernel
theorem s15_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 0 = true := by decide +kernel
theorem s15_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 1 = true := by decide +kernel
theorem s15_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 2 = true := by decide +kernel
theorem s15_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 3 = true := by decide +kernel
theorem k15_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k15_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k15_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s15_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k15_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k15_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 2 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k15_2_4_80 k h.1 (by omega)
theorem s15_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 5 = true := by decide +kernel
theorem s15_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 6 = true := by decide +kernel
theorem s15_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 2 7 = true := by decide +kernel
theorem s15_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 0 = true := by decide +kernel
theorem s15_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 1 = true := by decide +kernel
theorem s15_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 2 = true := by decide +kernel
theorem s15_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 3 = true := by decide +kernel
theorem k15_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k15_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k15_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s15_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k15_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k15_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 3 4).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k15_3_4_80 k h.1 (by omega)
theorem s15_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 5 = true := by decide +kernel
theorem s15_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 6 = true := by decide +kernel
theorem s15_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 3 7 = true := by decide +kernel
theorem s15_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 0 = true := by decide +kernel
theorem s15_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 1 = true := by decide +kernel
theorem s15_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 2 = true := by decide +kernel
theorem s15_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 3 = true := by decide +kernel
theorem s15_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 4 = true := by decide +kernel
theorem k15_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k15_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k15_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k15_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k15_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k15_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k15_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k15_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k15_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s15_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k15_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k15_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k15_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k15_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k15_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k15_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k15_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k15_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 5).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k15_4_5_40 k h.1 (by omega)
theorem k15_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k15_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k15_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k15_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k15_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k15_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k15_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k15_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k15_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k15_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k15_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s15_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k15_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k15_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k15_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k15_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k15_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k15_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k15_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k15_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k15_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k15_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 4 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k15_4_6_50 k h.1 (by omega)
theorem s15_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 4 7 = true := by decide +kernel
theorem s15_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 0 = true := by decide +kernel
theorem s15_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 1 = true := by decide +kernel
theorem s15_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 2 = true := by decide +kernel
theorem s15_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 3 = true := by decide +kernel
theorem s15_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 4 = true := by decide +kernel
theorem s15_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 5 = true := by decide +kernel
theorem k15_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k15_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k15_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k15_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k15_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k15_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s15_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k15_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k15_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k15_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k15_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k15_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 15) ((InDA2.TCasaD 2 5 6).getD (15 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k15_5_6_50 k h.1 (by omega)
theorem s15_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 5 7 = true := by decide +kernel
theorem col15_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 6 v) = true := by decide +kernel
theorem col15_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 7 v) = true := by decide +kernel
theorem col15 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 15) 15 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col15_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col15_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s15_2_0
    · exact s15_2_1
    · exact s15_2_2
    · exact s15_2_3
    · exact s15_2_4
    · exact s15_2_5
    · exact s15_2_6
    · exact s15_2_7
  · fin_cases v
    · exact s15_3_0
    · exact s15_3_1
    · exact s15_3_2
    · exact s15_3_3
    · exact s15_3_4
    · exact s15_3_5
    · exact s15_3_6
    · exact s15_3_7
  · fin_cases v
    · exact s15_4_0
    · exact s15_4_1
    · exact s15_4_2
    · exact s15_4_3
    · exact s15_4_4
    · exact s15_4_5
    · exact s15_4_6
    · exact s15_4_7
  · fin_cases v
    · exact s15_5_0
    · exact s15_5_1
    · exact s15_5_2
    · exact s15_5_3
    · exact s15_5_4
    · exact s15_5_5
    · exact s15_5_6
    · exact s15_5_7
  · exact List.all_eq_true.mp col15_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col15_7 v (List.mem_finRange v)
theorem col16_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 0 v) = true := by decide +kernel
theorem col16_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 1 v) = true := by decide +kernel
theorem s16_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 0 = true := by decide +kernel
theorem s16_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 1 = true := by decide +kernel
theorem s16_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 2 = true := by decide +kernel
theorem s16_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 3 = true := by decide +kernel
theorem k16_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k16_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k16_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s16_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k16_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k16_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TTsaaD 2 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k16_2_4_80 k h.1 (by omega)
theorem s16_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 5 = true := by decide +kernel
theorem s16_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 6 = true := by decide +kernel
theorem s16_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 2 7 = true := by decide +kernel
theorem s16_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 0 = true := by decide +kernel
theorem s16_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 1 = true := by decide +kernel
theorem s16_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 2 = true := by decide +kernel
theorem s16_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 3 = true := by decide +kernel
theorem k16_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k16_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k16_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s16_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k16_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k16_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 3 4).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k16_3_4_80 k h.1 (by omega)
theorem s16_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 5 = true := by decide +kernel
theorem s16_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 6 = true := by decide +kernel
theorem s16_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 3 7 = true := by decide +kernel
theorem s16_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 0 = true := by decide +kernel
theorem s16_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 1 = true := by decide +kernel
theorem s16_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 2 = true := by decide +kernel
theorem s16_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 3 = true := by decide +kernel
theorem s16_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 4 = true := by decide +kernel
theorem k16_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k16_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k16_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k16_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k16_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k16_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k16_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k16_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k16_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s16_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k16_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k16_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k16_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k16_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k16_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k16_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k16_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k16_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 5).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k16_4_5_40 k h.1 (by omega)
theorem k16_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k16_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k16_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k16_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k16_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k16_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k16_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k16_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k16_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k16_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k16_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s16_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k16_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k16_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k16_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k16_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k16_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k16_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k16_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k16_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k16_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k16_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 4 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k16_4_6_50 k h.1 (by omega)
theorem s16_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 4 7 = true := by decide +kernel
theorem s16_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 0 = true := by decide +kernel
theorem s16_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 1 = true := by decide +kernel
theorem s16_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 2 = true := by decide +kernel
theorem s16_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 3 = true := by decide +kernel
theorem s16_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 4 = true := by decide +kernel
theorem s16_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 5 = true := by decide +kernel
theorem k16_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k16_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k16_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k16_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k16_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k16_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s16_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k16_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k16_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k16_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k16_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k16_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 16) ((InDA2.TCasaD 3 5 6).getD (16 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k16_5_6_50 k h.1 (by omega)
theorem s16_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 5 7 = true := by decide +kernel
theorem col16_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 6 v) = true := by decide +kernel
theorem col16_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 7 v) = true := by decide +kernel
theorem col16 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 16) 16 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col16_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col16_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s16_2_0
    · exact s16_2_1
    · exact s16_2_2
    · exact s16_2_3
    · exact s16_2_4
    · exact s16_2_5
    · exact s16_2_6
    · exact s16_2_7
  · fin_cases v
    · exact s16_3_0
    · exact s16_3_1
    · exact s16_3_2
    · exact s16_3_3
    · exact s16_3_4
    · exact s16_3_5
    · exact s16_3_6
    · exact s16_3_7
  · fin_cases v
    · exact s16_4_0
    · exact s16_4_1
    · exact s16_4_2
    · exact s16_4_3
    · exact s16_4_4
    · exact s16_4_5
    · exact s16_4_6
    · exact s16_4_7
  · fin_cases v
    · exact s16_5_0
    · exact s16_5_1
    · exact s16_5_2
    · exact s16_5_3
    · exact s16_5_4
    · exact s16_5_5
    · exact s16_5_6
    · exact s16_5_7
  · exact List.all_eq_true.mp col16_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col16_7 v (List.mem_finRange v)
theorem col17_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 0 v) = true := by decide +kernel
theorem col17_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 1 v) = true := by decide +kernel
theorem s17_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 0 = true := by decide +kernel
theorem s17_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 1 = true := by decide +kernel
theorem s17_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 2 = true := by decide +kernel
theorem s17_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 3 = true := by decide +kernel
theorem k17_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k17_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k17_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s17_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k17_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k17_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TTsaaD 2 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k17_2_4_80 k h.1 (by omega)
theorem s17_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 5 = true := by decide +kernel
theorem s17_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 6 = true := by decide +kernel
theorem s17_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 2 7 = true := by decide +kernel
theorem s17_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 0 = true := by decide +kernel
theorem s17_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 1 = true := by decide +kernel
theorem s17_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 2 = true := by decide +kernel
theorem s17_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 3 = true := by decide +kernel
theorem k17_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k17_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k17_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s17_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k17_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k17_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 3 4).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k17_3_4_80 k h.1 (by omega)
theorem s17_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 5 = true := by decide +kernel
theorem s17_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 6 = true := by decide +kernel
theorem s17_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 3 7 = true := by decide +kernel
theorem s17_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 0 = true := by decide +kernel
theorem s17_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 1 = true := by decide +kernel
theorem s17_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 2 = true := by decide +kernel
theorem s17_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 3 = true := by decide +kernel
theorem s17_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 4 = true := by decide +kernel
theorem k17_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k17_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k17_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k17_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k17_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k17_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k17_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k17_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k17_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s17_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k17_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k17_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k17_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k17_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k17_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k17_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k17_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k17_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 5).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k17_4_5_40 k h.1 (by omega)
theorem k17_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k17_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k17_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k17_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k17_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k17_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k17_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k17_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k17_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k17_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k17_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s17_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k17_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k17_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k17_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k17_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k17_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k17_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k17_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k17_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k17_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k17_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 4 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k17_4_6_50 k h.1 (by omega)
theorem s17_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 4 7 = true := by decide +kernel
theorem s17_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 0 = true := by decide +kernel
theorem s17_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 1 = true := by decide +kernel
theorem s17_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 2 = true := by decide +kernel
theorem s17_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 3 = true := by decide +kernel
theorem s17_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 4 = true := by decide +kernel
theorem s17_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 5 = true := by decide +kernel
theorem k17_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k17_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k17_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k17_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k17_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k17_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s17_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k17_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k17_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k17_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k17_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k17_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 17) ((InDA2.TCasaD 3 5 6).getD (17 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k17_5_6_50 k h.1 (by omega)
theorem s17_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 5 7 = true := by decide +kernel
theorem col17_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 6 v) = true := by decide +kernel
theorem col17_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 7 v) = true := by decide +kernel
theorem col17 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 17) 17 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col17_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col17_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s17_2_0
    · exact s17_2_1
    · exact s17_2_2
    · exact s17_2_3
    · exact s17_2_4
    · exact s17_2_5
    · exact s17_2_6
    · exact s17_2_7
  · fin_cases v
    · exact s17_3_0
    · exact s17_3_1
    · exact s17_3_2
    · exact s17_3_3
    · exact s17_3_4
    · exact s17_3_5
    · exact s17_3_6
    · exact s17_3_7
  · fin_cases v
    · exact s17_4_0
    · exact s17_4_1
    · exact s17_4_2
    · exact s17_4_3
    · exact s17_4_4
    · exact s17_4_5
    · exact s17_4_6
    · exact s17_4_7
  · fin_cases v
    · exact s17_5_0
    · exact s17_5_1
    · exact s17_5_2
    · exact s17_5_3
    · exact s17_5_4
    · exact s17_5_5
    · exact s17_5_6
    · exact s17_5_7
  · exact List.all_eq_true.mp col17_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col17_7 v (List.mem_finRange v)
theorem col18_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 0 v) = true := by decide +kernel
theorem col18_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 1 v) = true := by decide +kernel
theorem s18_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 0 = true := by decide +kernel
theorem s18_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 1 = true := by decide +kernel
theorem s18_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 2 = true := by decide +kernel
theorem s18_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 3 = true := by decide +kernel
theorem k18_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k18_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k18_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s18_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k18_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k18_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TTsaaD 2 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k18_2_4_80 k h.1 (by omega)
theorem s18_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 5 = true := by decide +kernel
theorem s18_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 6 = true := by decide +kernel
theorem s18_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 2 7 = true := by decide +kernel
theorem s18_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 0 = true := by decide +kernel
theorem s18_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 1 = true := by decide +kernel
theorem s18_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 2 = true := by decide +kernel
theorem s18_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 3 = true := by decide +kernel
theorem k18_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k18_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k18_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s18_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k18_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k18_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 3 4).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k18_3_4_80 k h.1 (by omega)
theorem s18_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 5 = true := by decide +kernel
theorem s18_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 6 = true := by decide +kernel
theorem s18_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 3 7 = true := by decide +kernel
theorem s18_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 0 = true := by decide +kernel
theorem s18_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 1 = true := by decide +kernel
theorem s18_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 2 = true := by decide +kernel
theorem s18_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 3 = true := by decide +kernel
theorem s18_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 4 = true := by decide +kernel
theorem k18_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k18_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k18_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k18_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k18_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k18_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k18_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k18_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k18_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s18_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k18_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k18_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k18_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k18_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k18_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k18_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k18_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k18_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 5).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k18_4_5_40 k h.1 (by omega)
theorem k18_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k18_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k18_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k18_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k18_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k18_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k18_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k18_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k18_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k18_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k18_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s18_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k18_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k18_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k18_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k18_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k18_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k18_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k18_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k18_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k18_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k18_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 4 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k18_4_6_50 k h.1 (by omega)
theorem s18_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 4 7 = true := by decide +kernel
theorem s18_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 0 = true := by decide +kernel
theorem s18_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 1 = true := by decide +kernel
theorem s18_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 2 = true := by decide +kernel
theorem s18_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 3 = true := by decide +kernel
theorem s18_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 4 = true := by decide +kernel
theorem s18_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 5 = true := by decide +kernel
theorem k18_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k18_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k18_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k18_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k18_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k18_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s18_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k18_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k18_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k18_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k18_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k18_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 18) ((InDA2.TCasaD 3 5 6).getD (18 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k18_5_6_50 k h.1 (by omega)
theorem s18_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 5 7 = true := by decide +kernel
theorem col18_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 6 v) = true := by decide +kernel
theorem col18_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 7 v) = true := by decide +kernel
theorem col18 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 18) 18 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col18_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col18_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s18_2_0
    · exact s18_2_1
    · exact s18_2_2
    · exact s18_2_3
    · exact s18_2_4
    · exact s18_2_5
    · exact s18_2_6
    · exact s18_2_7
  · fin_cases v
    · exact s18_3_0
    · exact s18_3_1
    · exact s18_3_2
    · exact s18_3_3
    · exact s18_3_4
    · exact s18_3_5
    · exact s18_3_6
    · exact s18_3_7
  · fin_cases v
    · exact s18_4_0
    · exact s18_4_1
    · exact s18_4_2
    · exact s18_4_3
    · exact s18_4_4
    · exact s18_4_5
    · exact s18_4_6
    · exact s18_4_7
  · fin_cases v
    · exact s18_5_0
    · exact s18_5_1
    · exact s18_5_2
    · exact s18_5_3
    · exact s18_5_4
    · exact s18_5_5
    · exact s18_5_6
    · exact s18_5_7
  · exact List.all_eq_true.mp col18_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col18_7 v (List.mem_finRange v)
theorem col19_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 0 v) = true := by decide +kernel
theorem col19_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 1 v) = true := by decide +kernel
theorem s19_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 0 = true := by decide +kernel
theorem s19_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 1 = true := by decide +kernel
theorem s19_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 2 = true := by decide +kernel
theorem s19_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 3 = true := by decide +kernel
theorem k19_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k19_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k19_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s19_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k19_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k19_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TTsaaD 2 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k19_2_4_80 k h.1 (by omega)
theorem s19_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 5 = true := by decide +kernel
theorem s19_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 6 = true := by decide +kernel
theorem s19_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 2 7 = true := by decide +kernel
theorem s19_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 0 = true := by decide +kernel
theorem s19_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 1 = true := by decide +kernel
theorem s19_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 2 = true := by decide +kernel
theorem s19_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 3 = true := by decide +kernel
theorem k19_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k19_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k19_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s19_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k19_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k19_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 3 4).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k19_3_4_80 k h.1 (by omega)
theorem s19_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 5 = true := by decide +kernel
theorem s19_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 6 = true := by decide +kernel
theorem s19_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 3 7 = true := by decide +kernel
theorem s19_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 0 = true := by decide +kernel
theorem s19_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 1 = true := by decide +kernel
theorem s19_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 2 = true := by decide +kernel
theorem s19_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 3 = true := by decide +kernel
theorem s19_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 4 = true := by decide +kernel
theorem k19_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k19_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k19_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k19_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k19_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k19_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k19_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k19_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k19_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s19_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k19_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k19_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k19_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k19_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k19_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k19_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k19_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k19_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 5).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k19_4_5_40 k h.1 (by omega)
theorem k19_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k19_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k19_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k19_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k19_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k19_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k19_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k19_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k19_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k19_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k19_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s19_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k19_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k19_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k19_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k19_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k19_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k19_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k19_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k19_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k19_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k19_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 4 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k19_4_6_50 k h.1 (by omega)
theorem s19_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 4 7 = true := by decide +kernel
theorem s19_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 0 = true := by decide +kernel
theorem s19_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 1 = true := by decide +kernel
theorem s19_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 2 = true := by decide +kernel
theorem s19_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 3 = true := by decide +kernel
theorem s19_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 4 = true := by decide +kernel
theorem s19_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 5 = true := by decide +kernel
theorem k19_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k19_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k19_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k19_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k19_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k19_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s19_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k19_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k19_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k19_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k19_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k19_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 19) ((InDA2.TCasaD 3 5 6).getD (19 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k19_5_6_50 k h.1 (by omega)
theorem s19_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 5 7 = true := by decide +kernel
theorem col19_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 6 v) = true := by decide +kernel
theorem col19_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 7 v) = true := by decide +kernel
theorem col19 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 19) 19 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col19_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col19_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s19_2_0
    · exact s19_2_1
    · exact s19_2_2
    · exact s19_2_3
    · exact s19_2_4
    · exact s19_2_5
    · exact s19_2_6
    · exact s19_2_7
  · fin_cases v
    · exact s19_3_0
    · exact s19_3_1
    · exact s19_3_2
    · exact s19_3_3
    · exact s19_3_4
    · exact s19_3_5
    · exact s19_3_6
    · exact s19_3_7
  · fin_cases v
    · exact s19_4_0
    · exact s19_4_1
    · exact s19_4_2
    · exact s19_4_3
    · exact s19_4_4
    · exact s19_4_5
    · exact s19_4_6
    · exact s19_4_7
  · fin_cases v
    · exact s19_5_0
    · exact s19_5_1
    · exact s19_5_2
    · exact s19_5_3
    · exact s19_5_4
    · exact s19_5_5
    · exact s19_5_6
    · exact s19_5_7
  · exact List.all_eq_true.mp col19_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col19_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
