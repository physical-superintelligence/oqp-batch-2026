module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x555
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k147 : x2Key 1 := ⟨147, by decide⟩
x2_gj_cols gj269 269 1 5 5 5 256
theorem gjc147_0 : (List.range 11).all (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 269 (0 + d)) (gj269.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok147 : ∀ d < x2KeySize 1 k147, gjCheck 256 1 (x2KeyTypes 1 k147 0) (x2KeyTypes 1 k147 1) (x2KeyTypes 1 k147 2) (x2KeyMult 1 k147 0) (x2KeyMult 1 k147 1) (x2KeyMult 1 k147 2) (x2JCols (x2KeyGlobal 1 k147) d) (gj269.getD d 0) = true := by
  have hr : x2KeySize 1 k147 = 11 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 5 7 7 7 (x2JCols 269 d) (gj269.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 269 d) (gj269.getD d 0)) 0 11 gjc147_0 d (Nat.zero_le d) (by omega)
x2_nat_list K1x555k0c "verification/matrix-literals/x2-transfer/corr-light/K1x555k0.hex"
x2_nat_list A1x555k0c "verification/matrix-literals/x2-transfer/corr-light/A1x555k0.hex"
x2_vk_cols u269 gj269 K1x555k0c 256 343
x2_ua_cols ua269 u269 A1x555k0c 343 8
theorem cchk147 : corrKeyChk 1 k147 8 gj269 K1x555k0c u269 A1x555k0c ua269 := by
  have h1 : x2KeyDegree 1 k147 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k147 0 ∧ 1 ≤ x2KeyMult 1 k147 1 ∧ 1 ≤ x2KeyMult 1 k147 2 ∧ glRowOK 1 (x2KeyTypes 1 k147 0) (x2KeyMult 1 k147 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k147 1) (x2KeyMult 1 k147 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k147 2) (x2KeyMult 1 k147 2) 512 = true ∧ gj269.length = x2KeySize 1 k147 ∧ x2KeySize 1 k147 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 8, vCheck 256 (x2KeyMult 1 k147 0 * x2KeyMult 1 k147 1 * x2KeyMult 1 k147 2) (x2KeySize 1 k147) gj269 (K1x555k0c.getD c 0) (u269.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k147 0 * x2KeyMult 1 k147 1 * x2KeyMult 1 k147 2) (u269.getD c 0) = true := by decide +kernel
  have h3 : u269.length = 8 ∧ ua269.length = 8 ∧ 8 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 8, uaCheck (x2KeyMult 1 k147 0 * x2KeyMult 1 k147 1 * x2KeyMult 1 k147 2) 8 u269 (A1x555k0c.getD c 0) (ua269.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok147, h2, h3.1, h3.2.1, h3.2.2, h4⟩
def k148 : x2Key 1 := ⟨148, by decide⟩
x2_gj_cols gj270 270 1 5 5 5 256
theorem gjc148_0 : (List.range 7).all (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 270 (0 + d)) (gj270.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok148 : ∀ d < x2KeySize 1 k148, gjCheck 256 1 (x2KeyTypes 1 k148 0) (x2KeyTypes 1 k148 1) (x2KeyTypes 1 k148 2) (x2KeyMult 1 k148 0) (x2KeyMult 1 k148 1) (x2KeyMult 1 k148 2) (x2JCols (x2KeyGlobal 1 k148) d) (gj270.getD d 0) = true := by
  have hr : x2KeySize 1 k148 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 5 7 7 7 (x2JCols 270 d) (gj270.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 270 d) (gj270.getD d 0)) 0 7 gjc148_0 d (Nat.zero_le d) (by omega)
x2_v_cols v270 gj270 270 256 343
theorem vc148_0 : (List.range 4).all (fun c => vCheck 256 343 7 gj270 (x2Trial_270.getD (0 + c) 0) (v270.getD (0 + c) 0)) = true := by decide +kernel
theorem vok148 : ∀ c < 4, vCheck 256 (x2KeyMult 1 k148 0 * x2KeyMult 1 k148 1 * x2KeyMult 1 k148 2) (x2KeySize 1 k148) gj270 (x2Trial_270.getD c 0) (v270.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 7 gj270 (x2Trial_270.getD c 0) (v270.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 7 gj270 (x2Trial_270.getD c 0) (v270.getD c 0)) 0 4 vc148_0 c (Nat.zero_le c) (by omega)
theorem small148 : x2KeyDegree 1 k148 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k148 0 ∧ 1 ≤ x2KeyMult 1 k148 1 ∧ 1 ≤ x2KeyMult 1 k148 2 ∧ glRowOK 1 (x2KeyTypes 1 k148 0) (x2KeyMult 1 k148 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k148 1) (x2KeyMult 1 k148 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k148 2) (x2KeyMult 1 k148 2) 512 = true ∧ gj270.length = x2KeySize 1 k148 ∧ x2KeySize 1 k148 ≤ 512 ∧ v270.length = 4 := by decide +kernel
theorem chk148 : trialKeyChk 1 k148 4 gj270 x2Trial_270 v270 :=
  trialKeyChk_intro 1 k148 4 gj270 x2Trial_270 v270 small148 gjok148 vok148
def k149 : x2Key 1 := ⟨149, by decide⟩
x2_gj_cols gj271 271 1 5 5 5 256
theorem gjc149_0 : (List.range 18).all (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 271 (0 + d)) (gj271.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok149 : ∀ d < x2KeySize 1 k149, gjCheck 256 1 (x2KeyTypes 1 k149 0) (x2KeyTypes 1 k149 1) (x2KeyTypes 1 k149 2) (x2KeyMult 1 k149 0) (x2KeyMult 1 k149 1) (x2KeyMult 1 k149 2) (x2JCols (x2KeyGlobal 1 k149) d) (gj271.getD d 0) = true := by
  have hr : x2KeySize 1 k149 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 5 7 7 7 (x2JCols 271 d) (gj271.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 5 7 7 7 (x2JCols 271 d) (gj271.getD d 0)) 0 18 gjc149_0 d (Nat.zero_le d) (by omega)
x2_v_cols v271 gj271 271 256 343
theorem vc149_0 : (List.range 11).all (fun c => vCheck 256 343 18 gj271 (x2Trial_271.getD (0 + c) 0) (v271.getD (0 + c) 0)) = true := by decide +kernel
theorem vok149 : ∀ c < 11, vCheck 256 (x2KeyMult 1 k149 0 * x2KeyMult 1 k149 1 * x2KeyMult 1 k149 2) (x2KeySize 1 k149) gj271 (x2Trial_271.getD c 0) (v271.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 18 gj271 (x2Trial_271.getD c 0) (v271.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 18 gj271 (x2Trial_271.getD c 0) (v271.getD c 0)) 0 11 vc149_0 c (Nat.zero_le c) (by omega)
x2_p_cols p271 v271 7
theorem pok149 : ∀ c < 11, partnerCheck (x2KeyMult 1 k149 0) (v271.getD c 0) (p271.getD c 0) = true := by
  intro c hc
  show partnerCheck 7 (v271.getD c 0) (p271.getD c 0) = true
  have h : (List.range 11).all (fun c => partnerCheck 7 (v271.getD c 0) (p271.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small149 : x2KeyDegree 1 k149 = 2 ∧ x2KeyMult 1 k149 0 = x2KeyMult 1 k149 1 ∧ x2KeyMult 1 k149 1 = x2KeyMult 1 k149 2 ∧ 1 ≤ x2KeyMult 1 k149 0 ∧ glRowOK 1 (x2KeyTypes 1 k149 0) (x2KeyMult 1 k149 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k149 1) (x2KeyMult 1 k149 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k149 2) (x2KeyMult 1 k149 2) 512 = true ∧ gj271.length = x2KeySize 1 k149 ∧ x2KeySize 1 k149 ≤ 512 ∧ v271.length = 11 ∧ p271.length = 11 := by decide +kernel
theorem chk149 : trial2KeyChk 1 k149 11 gj271 x2Trial_271 v271 p271 :=
  trial2KeyChk_intro 1 k149 11 gj271 x2Trial_271 v271 p271 small149 gjok149 vok149 pok149

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k147, ibFS [(ua269, u269, 3)]), (k148, ibFS [(v270, v270, 94810963968000)]), (k149, ibFS [(v271, v271, 94810963968000), (p271, p271, 31603654656000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN147 : N k147 = x2CorrForm 1 k147 8 K1x555k0c A1x555k0c) (hN148 : N k148 = x2TrialForm 1 k148) (hN149 : N k149 = x2TrialForm 1 k149) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_corrChk 1 N k147 8 _ gj269 K1x555k0c u269 A1x555k0c ua269 (by decide) hN147 cchk147
  · exact keyOK_of_trialChk 1 N k148 4 _ gj270 x2Trial_270 v270 (by decide) (by rw [hN148]; exact trialForm_eq 1 k148 4 x2Trial_270 (by decide) rfl) chk148
  · exact keyOK_of_trial2Chk 1 N k149 11 _ gj271 x2Trial_271 v271 p271 (by decide) (by rw [hN149]; exact trialForm_eq 1 k149 11 x2Trial_271 (by decide) rfl) chk149

end ThreeCopyQutritWerner.X2.InK1x555
