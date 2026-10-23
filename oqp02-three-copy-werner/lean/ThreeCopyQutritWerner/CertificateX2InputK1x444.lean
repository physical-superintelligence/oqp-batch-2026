module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x444
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k129 : x2Key 1 := ⟨129, by decide⟩
x2_gj_cols gj251 251 1 4 4 4 256
theorem gjc129_0 : (List.range 14).all (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 251 (0 + d)) (gj251.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok129 : ∀ d < x2KeySize 1 k129, gjCheck 256 1 (x2KeyTypes 1 k129 0) (x2KeyTypes 1 k129 1) (x2KeyTypes 1 k129 2) (x2KeyMult 1 k129 0) (x2KeyMult 1 k129 1) (x2KeyMult 1 k129 2) (x2JCols (x2KeyGlobal 1 k129) d) (gj251.getD d 0) = true := by
  have hr : x2KeySize 1 k129 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 4 7 7 7 (x2JCols 251 d) (gj251.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 251 d) (gj251.getD d 0)) 0 14 gjc129_0 d (Nat.zero_le d) (by omega)
x2_nat_list K1x444k0c "verification/matrix-literals/x2-transfer/corr-light/K1x444k0.hex"
x2_nat_list A1x444k0c "verification/matrix-literals/x2-transfer/corr-light/A1x444k0.hex"
x2_vk_cols u251 gj251 K1x444k0c 256 343
x2_ua_cols ua251 u251 A1x444k0c 343 10
theorem cchk129 : corrKeyChk 1 k129 10 gj251 K1x444k0c u251 A1x444k0c ua251 := by
  have h1 : x2KeyDegree 1 k129 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k129 0 ∧ 1 ≤ x2KeyMult 1 k129 1 ∧ 1 ≤ x2KeyMult 1 k129 2 ∧ glRowOK 1 (x2KeyTypes 1 k129 0) (x2KeyMult 1 k129 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k129 1) (x2KeyMult 1 k129 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k129 2) (x2KeyMult 1 k129 2) 512 = true ∧ gj251.length = x2KeySize 1 k129 ∧ x2KeySize 1 k129 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 10, vCheck 256 (x2KeyMult 1 k129 0 * x2KeyMult 1 k129 1 * x2KeyMult 1 k129 2) (x2KeySize 1 k129) gj251 (K1x444k0c.getD c 0) (u251.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k129 0 * x2KeyMult 1 k129 1 * x2KeyMult 1 k129 2) (u251.getD c 0) = true := by decide +kernel
  have h3 : u251.length = 10 ∧ ua251.length = 10 ∧ 10 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 10, uaCheck (x2KeyMult 1 k129 0 * x2KeyMult 1 k129 1 * x2KeyMult 1 k129 2) 10 u251 (A1x444k0c.getD c 0) (ua251.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok129, h2, h3.1, h3.2.1, h3.2.2, h4⟩
def k130 : x2Key 1 := ⟨130, by decide⟩
x2_gj_cols gj252 252 1 4 4 4 256
theorem gjc130_0 : (List.range 5).all (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 252 (0 + d)) (gj252.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok130 : ∀ d < x2KeySize 1 k130, gjCheck 256 1 (x2KeyTypes 1 k130 0) (x2KeyTypes 1 k130 1) (x2KeyTypes 1 k130 2) (x2KeyMult 1 k130 0) (x2KeyMult 1 k130 1) (x2KeyMult 1 k130 2) (x2JCols (x2KeyGlobal 1 k130) d) (gj252.getD d 0) = true := by
  have hr : x2KeySize 1 k130 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 4 7 7 7 (x2JCols 252 d) (gj252.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 252 d) (gj252.getD d 0)) 0 5 gjc130_0 d (Nat.zero_le d) (by omega)
x2_v_cols v252 gj252 252 256 343
theorem vc130_0 : (List.range 2).all (fun c => vCheck 256 343 5 gj252 (x2Trial_252.getD (0 + c) 0) (v252.getD (0 + c) 0)) = true := by decide +kernel
theorem vok130 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k130 0 * x2KeyMult 1 k130 1 * x2KeyMult 1 k130 2) (x2KeySize 1 k130) gj252 (x2Trial_252.getD c 0) (v252.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 5 gj252 (x2Trial_252.getD c 0) (v252.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 5 gj252 (x2Trial_252.getD c 0) (v252.getD c 0)) 0 2 vc130_0 c (Nat.zero_le c) (by omega)
theorem small130 : x2KeyDegree 1 k130 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k130 0 ∧ 1 ≤ x2KeyMult 1 k130 1 ∧ 1 ≤ x2KeyMult 1 k130 2 ∧ glRowOK 1 (x2KeyTypes 1 k130 0) (x2KeyMult 1 k130 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k130 1) (x2KeyMult 1 k130 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k130 2) (x2KeyMult 1 k130 2) 512 = true ∧ gj252.length = x2KeySize 1 k130 ∧ x2KeySize 1 k130 ≤ 512 ∧ v252.length = 2 := by decide +kernel
theorem chk130 : trialKeyChk 1 k130 2 gj252 x2Trial_252 v252 :=
  trialKeyChk_intro 1 k130 2 gj252 x2Trial_252 v252 small130 gjok130 vok130
def k131 : x2Key 1 := ⟨131, by decide⟩
x2_gj_cols gj253 253 1 4 4 4 256
theorem gjc131_0 : (List.range 19).all (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 253 (0 + d)) (gj253.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok131 : ∀ d < x2KeySize 1 k131, gjCheck 256 1 (x2KeyTypes 1 k131 0) (x2KeyTypes 1 k131 1) (x2KeyTypes 1 k131 2) (x2KeyMult 1 k131 0) (x2KeyMult 1 k131 1) (x2KeyMult 1 k131 2) (x2JCols (x2KeyGlobal 1 k131) d) (gj253.getD d 0) = true := by
  have hr : x2KeySize 1 k131 = 19 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 4 7 7 7 (x2JCols 253 d) (gj253.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 4 7 7 7 (x2JCols 253 d) (gj253.getD d 0)) 0 19 gjc131_0 d (Nat.zero_le d) (by omega)
x2_v_cols v253 gj253 253 256 343
theorem vc131_0 : (List.range 11).all (fun c => vCheck 256 343 19 gj253 (x2Trial_253.getD (0 + c) 0) (v253.getD (0 + c) 0)) = true := by decide +kernel
theorem vok131 : ∀ c < 11, vCheck 256 (x2KeyMult 1 k131 0 * x2KeyMult 1 k131 1 * x2KeyMult 1 k131 2) (x2KeySize 1 k131) gj253 (x2Trial_253.getD c 0) (v253.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 19 gj253 (x2Trial_253.getD c 0) (v253.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 19 gj253 (x2Trial_253.getD c 0) (v253.getD c 0)) 0 11 vc131_0 c (Nat.zero_le c) (by omega)
x2_p_cols p253 v253 7
theorem pok131 : ∀ c < 11, partnerCheck (x2KeyMult 1 k131 0) (v253.getD c 0) (p253.getD c 0) = true := by
  intro c hc
  show partnerCheck 7 (v253.getD c 0) (p253.getD c 0) = true
  have h : (List.range 11).all (fun c => partnerCheck 7 (v253.getD c 0) (p253.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small131 : x2KeyDegree 1 k131 = 2 ∧ x2KeyMult 1 k131 0 = x2KeyMult 1 k131 1 ∧ x2KeyMult 1 k131 1 = x2KeyMult 1 k131 2 ∧ 1 ≤ x2KeyMult 1 k131 0 ∧ glRowOK 1 (x2KeyTypes 1 k131 0) (x2KeyMult 1 k131 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k131 1) (x2KeyMult 1 k131 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k131 2) (x2KeyMult 1 k131 2) 512 = true ∧ gj253.length = x2KeySize 1 k131 ∧ x2KeySize 1 k131 ≤ 512 ∧ v253.length = 11 ∧ p253.length = 11 := by decide +kernel
theorem chk131 : trial2KeyChk 1 k131 11 gj253 x2Trial_253 v253 p253 :=
  trial2KeyChk_intro 1 k131 11 gj253 x2Trial_253 v253 p253 small131 gjok131 vok131 pok131

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k129, ibFS [(ua251, u251, 3)]), (k130, ibFS [(v252, v252, 94810963968000)]), (k131, ibFS [(v253, v253, 94810963968000), (p253, p253, 31603654656000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN129 : N k129 = x2CorrForm 1 k129 10 K1x444k0c A1x444k0c) (hN130 : N k130 = x2TrialForm 1 k130) (hN131 : N k131 = x2TrialForm 1 k131) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 4 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_corrChk 1 N k129 10 _ gj251 K1x444k0c u251 A1x444k0c ua251 (by decide) hN129 cchk129
  · exact keyOK_of_trialChk 1 N k130 2 _ gj252 x2Trial_252 v252 (by decide) (by rw [hN130]; exact trialForm_eq 1 k130 2 x2Trial_252 (by decide) rfl) chk130
  · exact keyOK_of_trial2Chk 1 N k131 11 _ gj253 x2Trial_253 v253 p253 (by decide) (by rw [hN131]; exact trialForm_eq 1 k131 11 x2Trial_253 (by decide) rfl) chk131

end ThreeCopyQutritWerner.X2.InK1x444
