module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [20, 25). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col20_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 0 v) = true := by decide +kernel
theorem col20_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 1 v) = true := by decide +kernel
theorem s20_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 0 = true := by decide +kernel
theorem s20_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 1 = true := by decide +kernel
theorem s20_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 2 = true := by decide +kernel
theorem s20_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 3 = true := by decide +kernel
theorem k20_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k20_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k20_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s20_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k20_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k20_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TTsaaD 2 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k20_2_4_80 k h.1 (by omega)
theorem s20_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 5 = true := by decide +kernel
theorem s20_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 6 = true := by decide +kernel
theorem s20_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 2 7 = true := by decide +kernel
theorem s20_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 0 = true := by decide +kernel
theorem s20_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 1 = true := by decide +kernel
theorem s20_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 2 = true := by decide +kernel
theorem s20_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 3 = true := by decide +kernel
theorem k20_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k20_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k20_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s20_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k20_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k20_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 3 4).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k20_3_4_80 k h.1 (by omega)
theorem s20_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 5 = true := by decide +kernel
theorem s20_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 6 = true := by decide +kernel
theorem s20_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 3 7 = true := by decide +kernel
theorem s20_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 0 = true := by decide +kernel
theorem s20_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 1 = true := by decide +kernel
theorem s20_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 2 = true := by decide +kernel
theorem s20_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 3 = true := by decide +kernel
theorem s20_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 4 = true := by decide +kernel
theorem k20_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k20_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k20_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k20_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k20_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k20_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k20_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k20_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k20_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s20_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k20_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k20_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k20_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k20_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k20_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k20_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k20_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k20_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 5).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k20_4_5_40 k h.1 (by omega)
theorem k20_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k20_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k20_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k20_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k20_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k20_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k20_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k20_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k20_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k20_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k20_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s20_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k20_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k20_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k20_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k20_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k20_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k20_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k20_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k20_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k20_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k20_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 4 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k20_4_6_50 k h.1 (by omega)
theorem s20_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 4 7 = true := by decide +kernel
theorem s20_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 0 = true := by decide +kernel
theorem s20_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 1 = true := by decide +kernel
theorem s20_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 2 = true := by decide +kernel
theorem s20_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 3 = true := by decide +kernel
theorem s20_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 4 = true := by decide +kernel
theorem s20_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 5 = true := by decide +kernel
theorem k20_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k20_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k20_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k20_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k20_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k20_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s20_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k20_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k20_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k20_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k20_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k20_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 20) ((InDA2.TCasaD 3 5 6).getD (20 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k20_5_6_50 k h.1 (by omega)
theorem s20_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 5 7 = true := by decide +kernel
theorem col20_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 6 v) = true := by decide +kernel
theorem col20_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 7 v) = true := by decide +kernel
theorem col20 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 20) 20 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col20_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col20_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s20_2_0
    · exact s20_2_1
    · exact s20_2_2
    · exact s20_2_3
    · exact s20_2_4
    · exact s20_2_5
    · exact s20_2_6
    · exact s20_2_7
  · fin_cases v
    · exact s20_3_0
    · exact s20_3_1
    · exact s20_3_2
    · exact s20_3_3
    · exact s20_3_4
    · exact s20_3_5
    · exact s20_3_6
    · exact s20_3_7
  · fin_cases v
    · exact s20_4_0
    · exact s20_4_1
    · exact s20_4_2
    · exact s20_4_3
    · exact s20_4_4
    · exact s20_4_5
    · exact s20_4_6
    · exact s20_4_7
  · fin_cases v
    · exact s20_5_0
    · exact s20_5_1
    · exact s20_5_2
    · exact s20_5_3
    · exact s20_5_4
    · exact s20_5_5
    · exact s20_5_6
    · exact s20_5_7
  · exact List.all_eq_true.mp col20_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col20_7 v (List.mem_finRange v)
theorem col21_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 0 v) = true := by decide +kernel
theorem col21_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 1 v) = true := by decide +kernel
theorem s21_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 0 = true := by decide +kernel
theorem s21_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 1 = true := by decide +kernel
theorem s21_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 2 = true := by decide +kernel
theorem s21_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 3 = true := by decide +kernel
theorem k21_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k21_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k21_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s21_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k21_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k21_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TTsaaD 2 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k21_2_4_80 k h.1 (by omega)
theorem s21_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 5 = true := by decide +kernel
theorem s21_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 6 = true := by decide +kernel
theorem s21_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 2 7 = true := by decide +kernel
theorem s21_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 0 = true := by decide +kernel
theorem s21_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 1 = true := by decide +kernel
theorem s21_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 2 = true := by decide +kernel
theorem s21_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 3 = true := by decide +kernel
theorem k21_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k21_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k21_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s21_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k21_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k21_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 3 4).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k21_3_4_80 k h.1 (by omega)
theorem s21_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 5 = true := by decide +kernel
theorem s21_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 6 = true := by decide +kernel
theorem s21_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 3 7 = true := by decide +kernel
theorem s21_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 0 = true := by decide +kernel
theorem s21_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 1 = true := by decide +kernel
theorem s21_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 2 = true := by decide +kernel
theorem s21_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 3 = true := by decide +kernel
theorem s21_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 4 = true := by decide +kernel
theorem k21_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k21_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k21_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k21_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k21_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k21_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k21_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k21_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k21_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s21_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k21_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k21_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k21_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k21_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k21_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k21_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k21_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k21_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 5).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k21_4_5_40 k h.1 (by omega)
theorem k21_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k21_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k21_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k21_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k21_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k21_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k21_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k21_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k21_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k21_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k21_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s21_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k21_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k21_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k21_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k21_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k21_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k21_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k21_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k21_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k21_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k21_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 4 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k21_4_6_50 k h.1 (by omega)
theorem s21_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 4 7 = true := by decide +kernel
theorem s21_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 0 = true := by decide +kernel
theorem s21_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 1 = true := by decide +kernel
theorem s21_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 2 = true := by decide +kernel
theorem s21_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 3 = true := by decide +kernel
theorem s21_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 4 = true := by decide +kernel
theorem s21_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 5 = true := by decide +kernel
theorem k21_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k21_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k21_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k21_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k21_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k21_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s21_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k21_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k21_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k21_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k21_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k21_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 21) ((InDA2.TCasaD 3 5 6).getD (21 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k21_5_6_50 k h.1 (by omega)
theorem s21_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 5 7 = true := by decide +kernel
theorem col21_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 6 v) = true := by decide +kernel
theorem col21_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 7 v) = true := by decide +kernel
theorem col21 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 21) 21 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col21_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col21_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s21_2_0
    · exact s21_2_1
    · exact s21_2_2
    · exact s21_2_3
    · exact s21_2_4
    · exact s21_2_5
    · exact s21_2_6
    · exact s21_2_7
  · fin_cases v
    · exact s21_3_0
    · exact s21_3_1
    · exact s21_3_2
    · exact s21_3_3
    · exact s21_3_4
    · exact s21_3_5
    · exact s21_3_6
    · exact s21_3_7
  · fin_cases v
    · exact s21_4_0
    · exact s21_4_1
    · exact s21_4_2
    · exact s21_4_3
    · exact s21_4_4
    · exact s21_4_5
    · exact s21_4_6
    · exact s21_4_7
  · fin_cases v
    · exact s21_5_0
    · exact s21_5_1
    · exact s21_5_2
    · exact s21_5_3
    · exact s21_5_4
    · exact s21_5_5
    · exact s21_5_6
    · exact s21_5_7
  · exact List.all_eq_true.mp col21_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col21_7 v (List.mem_finRange v)
theorem col22_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 0 v) = true := by decide +kernel
theorem col22_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 1 v) = true := by decide +kernel
theorem s22_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 0 = true := by decide +kernel
theorem s22_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 1 = true := by decide +kernel
theorem s22_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 2 = true := by decide +kernel
theorem s22_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 3 = true := by decide +kernel
theorem k22_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k22_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k22_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s22_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k22_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k22_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TTsaaD 2 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k22_2_4_80 k h.1 (by omega)
theorem s22_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 5 = true := by decide +kernel
theorem s22_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 6 = true := by decide +kernel
theorem s22_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 2 7 = true := by decide +kernel
theorem s22_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 0 = true := by decide +kernel
theorem s22_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 1 = true := by decide +kernel
theorem s22_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 2 = true := by decide +kernel
theorem s22_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 3 = true := by decide +kernel
theorem k22_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k22_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k22_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s22_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k22_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k22_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 3 4).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k22_3_4_80 k h.1 (by omega)
theorem s22_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 5 = true := by decide +kernel
theorem s22_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 6 = true := by decide +kernel
theorem s22_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 3 7 = true := by decide +kernel
theorem s22_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 0 = true := by decide +kernel
theorem s22_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 1 = true := by decide +kernel
theorem s22_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 2 = true := by decide +kernel
theorem s22_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 3 = true := by decide +kernel
theorem s22_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 4 = true := by decide +kernel
theorem k22_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k22_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k22_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k22_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k22_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k22_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k22_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k22_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k22_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s22_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k22_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k22_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k22_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k22_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k22_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k22_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k22_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k22_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 5).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k22_4_5_40 k h.1 (by omega)
theorem k22_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k22_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k22_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k22_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k22_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k22_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k22_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k22_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k22_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k22_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k22_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s22_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k22_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k22_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k22_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k22_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k22_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k22_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k22_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k22_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k22_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k22_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 4 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k22_4_6_50 k h.1 (by omega)
theorem s22_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 4 7 = true := by decide +kernel
theorem s22_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 0 = true := by decide +kernel
theorem s22_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 1 = true := by decide +kernel
theorem s22_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 2 = true := by decide +kernel
theorem s22_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 3 = true := by decide +kernel
theorem s22_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 4 = true := by decide +kernel
theorem s22_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 5 = true := by decide +kernel
theorem k22_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k22_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k22_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k22_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k22_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k22_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s22_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k22_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k22_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k22_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k22_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k22_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 22) ((InDA2.TCasaD 3 5 6).getD (22 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k22_5_6_50 k h.1 (by omega)
theorem s22_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 5 7 = true := by decide +kernel
theorem col22_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 6 v) = true := by decide +kernel
theorem col22_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 7 v) = true := by decide +kernel
theorem col22 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 22) 22 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col22_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col22_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s22_2_0
    · exact s22_2_1
    · exact s22_2_2
    · exact s22_2_3
    · exact s22_2_4
    · exact s22_2_5
    · exact s22_2_6
    · exact s22_2_7
  · fin_cases v
    · exact s22_3_0
    · exact s22_3_1
    · exact s22_3_2
    · exact s22_3_3
    · exact s22_3_4
    · exact s22_3_5
    · exact s22_3_6
    · exact s22_3_7
  · fin_cases v
    · exact s22_4_0
    · exact s22_4_1
    · exact s22_4_2
    · exact s22_4_3
    · exact s22_4_4
    · exact s22_4_5
    · exact s22_4_6
    · exact s22_4_7
  · fin_cases v
    · exact s22_5_0
    · exact s22_5_1
    · exact s22_5_2
    · exact s22_5_3
    · exact s22_5_4
    · exact s22_5_5
    · exact s22_5_6
    · exact s22_5_7
  · exact List.all_eq_true.mp col22_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col22_7 v (List.mem_finRange v)
theorem col23_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 0 v) = true := by decide +kernel
theorem col23_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 1 v) = true := by decide +kernel
theorem s23_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 0 = true := by decide +kernel
theorem s23_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 1 = true := by decide +kernel
theorem s23_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 2 = true := by decide +kernel
theorem s23_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 3 = true := by decide +kernel
theorem k23_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k23_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k23_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s23_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k23_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k23_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TTsaaD 2 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k23_2_4_80 k h.1 (by omega)
theorem s23_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 5 = true := by decide +kernel
theorem s23_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 6 = true := by decide +kernel
theorem s23_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 2 7 = true := by decide +kernel
theorem s23_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 0 = true := by decide +kernel
theorem s23_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 1 = true := by decide +kernel
theorem s23_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 2 = true := by decide +kernel
theorem s23_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 3 = true := by decide +kernel
theorem k23_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k23_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k23_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s23_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k23_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k23_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 3 4).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k23_3_4_80 k h.1 (by omega)
theorem s23_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 5 = true := by decide +kernel
theorem s23_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 6 = true := by decide +kernel
theorem s23_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 3 7 = true := by decide +kernel
theorem s23_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 0 = true := by decide +kernel
theorem s23_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 1 = true := by decide +kernel
theorem s23_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 2 = true := by decide +kernel
theorem s23_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 3 = true := by decide +kernel
theorem s23_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 4 = true := by decide +kernel
theorem k23_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k23_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k23_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k23_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k23_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k23_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k23_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k23_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k23_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s23_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k23_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k23_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k23_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k23_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k23_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k23_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k23_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k23_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 5).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k23_4_5_40 k h.1 (by omega)
theorem k23_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k23_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k23_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k23_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k23_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k23_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k23_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k23_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k23_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k23_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k23_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s23_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k23_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k23_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k23_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k23_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k23_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k23_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k23_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k23_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k23_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k23_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 4 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k23_4_6_50 k h.1 (by omega)
theorem s23_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 4 7 = true := by decide +kernel
theorem s23_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 0 = true := by decide +kernel
theorem s23_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 1 = true := by decide +kernel
theorem s23_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 2 = true := by decide +kernel
theorem s23_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 3 = true := by decide +kernel
theorem s23_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 4 = true := by decide +kernel
theorem s23_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 5 = true := by decide +kernel
theorem k23_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k23_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k23_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k23_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k23_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k23_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s23_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k23_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k23_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k23_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k23_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k23_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 23) ((InDA2.TCasaD 3 5 6).getD (23 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k23_5_6_50 k h.1 (by omega)
theorem s23_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 5 7 = true := by decide +kernel
theorem col23_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 6 v) = true := by decide +kernel
theorem col23_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 7 v) = true := by decide +kernel
theorem col23 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 23) 23 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col23_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col23_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s23_2_0
    · exact s23_2_1
    · exact s23_2_2
    · exact s23_2_3
    · exact s23_2_4
    · exact s23_2_5
    · exact s23_2_6
    · exact s23_2_7
  · fin_cases v
    · exact s23_3_0
    · exact s23_3_1
    · exact s23_3_2
    · exact s23_3_3
    · exact s23_3_4
    · exact s23_3_5
    · exact s23_3_6
    · exact s23_3_7
  · fin_cases v
    · exact s23_4_0
    · exact s23_4_1
    · exact s23_4_2
    · exact s23_4_3
    · exact s23_4_4
    · exact s23_4_5
    · exact s23_4_6
    · exact s23_4_7
  · fin_cases v
    · exact s23_5_0
    · exact s23_5_1
    · exact s23_5_2
    · exact s23_5_3
    · exact s23_5_4
    · exact s23_5_5
    · exact s23_5_6
    · exact s23_5_7
  · exact List.all_eq_true.mp col23_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col23_7 v (List.mem_finRange v)
theorem col24_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 0 v) = true := by decide +kernel
theorem col24_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 1 v) = true := by decide +kernel
theorem s24_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 0 = true := by decide +kernel
theorem s24_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 1 = true := by decide +kernel
theorem s24_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 2 = true := by decide +kernel
theorem s24_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 3 = true := by decide +kernel
theorem k24_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k24_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k24_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s24_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 4 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k24_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k24_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TTsaaD 2 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k24_2_4_80 k h.1 (by omega)
theorem s24_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 5 = true := by decide +kernel
theorem s24_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 6 = true := by decide +kernel
theorem s24_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 2 7 = true := by decide +kernel
theorem s24_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 0 = true := by decide +kernel
theorem s24_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 1 = true := by decide +kernel
theorem s24_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 2 = true := by decide +kernel
theorem s24_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 3 = true := by decide +kernel
theorem k24_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k24_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k24_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s24_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k24_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k24_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 3 4).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k24_3_4_80 k h.1 (by omega)
theorem s24_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 5 = true := by decide +kernel
theorem s24_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 6 = true := by decide +kernel
theorem s24_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 3 7 = true := by decide +kernel
theorem s24_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 0 = true := by decide +kernel
theorem s24_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 1 = true := by decide +kernel
theorem s24_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 2 = true := by decide +kernel
theorem s24_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 3 = true := by decide +kernel
theorem s24_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 4 = true := by decide +kernel
theorem k24_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k24_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k24_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k24_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k24_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k24_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k24_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k24_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k24_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s24_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k24_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k24_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k24_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k24_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k24_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k24_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k24_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k24_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 5).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k24_4_5_40 k h.1 (by omega)
theorem k24_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k24_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k24_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k24_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k24_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k24_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k24_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k24_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k24_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k24_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k24_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s24_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k24_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k24_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k24_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k24_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k24_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k24_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k24_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k24_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k24_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k24_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 4 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k24_4_6_50 k h.1 (by omega)
theorem s24_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 4 7 = true := by decide +kernel
theorem s24_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 0 = true := by decide +kernel
theorem s24_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 1 = true := by decide +kernel
theorem s24_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 2 = true := by decide +kernel
theorem s24_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 3 = true := by decide +kernel
theorem s24_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 4 = true := by decide +kernel
theorem s24_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 5 = true := by decide +kernel
theorem k24_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k24_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k24_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k24_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k24_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k24_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s24_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k24_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k24_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k24_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k24_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k24_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 24) ((InDA2.TCasaD 3 5 6).getD (24 - x2AOff 2 3) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k24_5_6_50 k h.1 (by omega)
theorem s24_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 5 7 = true := by decide +kernel
theorem col24_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 6 v) = true := by decide +kernel
theorem col24_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 7 v) = true := by decide +kernel
theorem col24 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 24) 24 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col24_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col24_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s24_2_0
    · exact s24_2_1
    · exact s24_2_2
    · exact s24_2_3
    · exact s24_2_4
    · exact s24_2_5
    · exact s24_2_6
    · exact s24_2_7
  · fin_cases v
    · exact s24_3_0
    · exact s24_3_1
    · exact s24_3_2
    · exact s24_3_3
    · exact s24_3_4
    · exact s24_3_5
    · exact s24_3_6
    · exact s24_3_7
  · fin_cases v
    · exact s24_4_0
    · exact s24_4_1
    · exact s24_4_2
    · exact s24_4_3
    · exact s24_4_4
    · exact s24_4_5
    · exact s24_4_6
    · exact s24_4_7
  · fin_cases v
    · exact s24_5_0
    · exact s24_5_1
    · exact s24_5_2
    · exact s24_5_3
    · exact s24_5_4
    · exact s24_5_5
    · exact s24_5_6
    · exact s24_5_7
  · exact List.all_eq_true.mp col24_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col24_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
