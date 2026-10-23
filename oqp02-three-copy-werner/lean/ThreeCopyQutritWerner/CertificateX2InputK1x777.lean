module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (7, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x777
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k166 : x2Key 1 := ⟨166, by decide⟩
x2_gj_cols gj288 288 1 7 7 7 256
theorem gjc166_0 : (List.range 9).all (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 288 (0 + d)) (gj288.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok166 : ∀ d < x2KeySize 1 k166, gjCheck 256 1 (x2KeyTypes 1 k166 0) (x2KeyTypes 1 k166 1) (x2KeyTypes 1 k166 2) (x2KeyMult 1 k166 0) (x2KeyMult 1 k166 1) (x2KeyMult 1 k166 2) (x2JCols (x2KeyGlobal 1 k166) d) (gj288.getD d 0) = true := by
  have hr : x2KeySize 1 k166 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 7 7 7 6 6 6 (x2JCols 288 d) (gj288.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 288 d) (gj288.getD d 0)) 0 9 gjc166_0 d (Nat.zero_le d) (by omega)
x2_v_cols v288 gj288 288 256 216
theorem vc166_0 : (List.range 4).all (fun c => vCheck 256 216 9 gj288 (x2Trial_288.getD (0 + c) 0) (v288.getD (0 + c) 0)) = true := by decide +kernel
theorem vok166 : ∀ c < 4, vCheck 256 (x2KeyMult 1 k166 0 * x2KeyMult 1 k166 1 * x2KeyMult 1 k166 2) (x2KeySize 1 k166) gj288 (x2Trial_288.getD c 0) (v288.getD c 0) = true := by
  intro c hc
  show vCheck 256 216 9 gj288 (x2Trial_288.getD c 0) (v288.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 216 9 gj288 (x2Trial_288.getD c 0) (v288.getD c 0)) 0 4 vc166_0 c (Nat.zero_le c) (by omega)
theorem small166 : x2KeyDegree 1 k166 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k166 0 ∧ 1 ≤ x2KeyMult 1 k166 1 ∧ 1 ≤ x2KeyMult 1 k166 2 ∧ glRowOK 1 (x2KeyTypes 1 k166 0) (x2KeyMult 1 k166 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k166 1) (x2KeyMult 1 k166 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k166 2) (x2KeyMult 1 k166 2) 512 = true ∧ gj288.length = x2KeySize 1 k166 ∧ x2KeySize 1 k166 ≤ 512 ∧ v288.length = 4 := by decide +kernel
theorem chk166 : trialKeyChk 1 k166 4 gj288 x2Trial_288 v288 :=
  trialKeyChk_intro 1 k166 4 gj288 x2Trial_288 v288 small166 gjok166 vok166
def k167 : x2Key 1 := ⟨167, by decide⟩
x2_gj_cols gj289 289 1 7 7 7 256
theorem gjc167_0 : (List.range 3).all (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 289 (0 + d)) (gj289.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok167 : ∀ d < x2KeySize 1 k167, gjCheck 256 1 (x2KeyTypes 1 k167 0) (x2KeyTypes 1 k167 1) (x2KeyTypes 1 k167 2) (x2KeyMult 1 k167 0) (x2KeyMult 1 k167 1) (x2KeyMult 1 k167 2) (x2JCols (x2KeyGlobal 1 k167) d) (gj289.getD d 0) = true := by
  have hr : x2KeySize 1 k167 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 7 7 7 6 6 6 (x2JCols 289 d) (gj289.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 289 d) (gj289.getD d 0)) 0 3 gjc167_0 d (Nat.zero_le d) (by omega)
x2_v_cols v289 gj289 289 256 216
theorem vc167_0 : (List.range 3).all (fun c => vCheck 256 216 3 gj289 (x2Trial_289.getD (0 + c) 0) (v289.getD (0 + c) 0)) = true := by decide +kernel
theorem vok167 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k167 0 * x2KeyMult 1 k167 1 * x2KeyMult 1 k167 2) (x2KeySize 1 k167) gj289 (x2Trial_289.getD c 0) (v289.getD c 0) = true := by
  intro c hc
  show vCheck 256 216 3 gj289 (x2Trial_289.getD c 0) (v289.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 216 3 gj289 (x2Trial_289.getD c 0) (v289.getD c 0)) 0 3 vc167_0 c (Nat.zero_le c) (by omega)
theorem small167 : x2KeyDegree 1 k167 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k167 0 ∧ 1 ≤ x2KeyMult 1 k167 1 ∧ 1 ≤ x2KeyMult 1 k167 2 ∧ glRowOK 1 (x2KeyTypes 1 k167 0) (x2KeyMult 1 k167 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k167 1) (x2KeyMult 1 k167 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k167 2) (x2KeyMult 1 k167 2) 512 = true ∧ gj289.length = x2KeySize 1 k167 ∧ x2KeySize 1 k167 ≤ 512 ∧ v289.length = 3 := by decide +kernel
theorem chk167 : trialKeyChk 1 k167 3 gj289 x2Trial_289 v289 :=
  trialKeyChk_intro 1 k167 3 gj289 x2Trial_289 v289 small167 gjok167 vok167
def k168 : x2Key 1 := ⟨168, by decide⟩
x2_gj_cols gj290 290 1 7 7 7 256
theorem gjc168_0 : (List.range 12).all (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 290 (0 + d)) (gj290.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok168 : ∀ d < x2KeySize 1 k168, gjCheck 256 1 (x2KeyTypes 1 k168 0) (x2KeyTypes 1 k168 1) (x2KeyTypes 1 k168 2) (x2KeyMult 1 k168 0) (x2KeyMult 1 k168 1) (x2KeyMult 1 k168 2) (x2JCols (x2KeyGlobal 1 k168) d) (gj290.getD d 0) = true := by
  have hr : x2KeySize 1 k168 = 12 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 7 7 7 6 6 6 (x2JCols 290 d) (gj290.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 7 7 7 6 6 6 (x2JCols 290 d) (gj290.getD d 0)) 0 12 gjc168_0 d (Nat.zero_le d) (by omega)
x2_v_cols v290 gj290 290 256 216
theorem vc168_0 : (List.range 7).all (fun c => vCheck 256 216 12 gj290 (x2Trial_290.getD (0 + c) 0) (v290.getD (0 + c) 0)) = true := by decide +kernel
theorem vok168 : ∀ c < 7, vCheck 256 (x2KeyMult 1 k168 0 * x2KeyMult 1 k168 1 * x2KeyMult 1 k168 2) (x2KeySize 1 k168) gj290 (x2Trial_290.getD c 0) (v290.getD c 0) = true := by
  intro c hc
  show vCheck 256 216 12 gj290 (x2Trial_290.getD c 0) (v290.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 216 12 gj290 (x2Trial_290.getD c 0) (v290.getD c 0)) 0 7 vc168_0 c (Nat.zero_le c) (by omega)
x2_p_cols p290 v290 6
theorem pok168 : ∀ c < 7, partnerCheck (x2KeyMult 1 k168 0) (v290.getD c 0) (p290.getD c 0) = true := by
  intro c hc
  show partnerCheck 6 (v290.getD c 0) (p290.getD c 0) = true
  have h : (List.range 7).all (fun c => partnerCheck 6 (v290.getD c 0) (p290.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small168 : x2KeyDegree 1 k168 = 2 ∧ x2KeyMult 1 k168 0 = x2KeyMult 1 k168 1 ∧ x2KeyMult 1 k168 1 = x2KeyMult 1 k168 2 ∧ 1 ≤ x2KeyMult 1 k168 0 ∧ glRowOK 1 (x2KeyTypes 1 k168 0) (x2KeyMult 1 k168 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k168 1) (x2KeyMult 1 k168 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k168 2) (x2KeyMult 1 k168 2) 512 = true ∧ gj290.length = x2KeySize 1 k168 ∧ x2KeySize 1 k168 ≤ 512 ∧ v290.length = 7 ∧ p290.length = 7 := by decide +kernel
theorem chk168 : trial2KeyChk 1 k168 7 gj290 x2Trial_290 v290 p290 :=
  trial2KeyChk_intro 1 k168 7 gj290 x2Trial_290 v290 p290 small168 gjok168 vok168 pok168

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k166, ibFS [(v288, v288, 94810963968000)]), (k167, ibFS [(v289, v289, 94810963968000)]), (k168, ibFS [(v290, v290, 94810963968000), (p290, p290, 31603654656000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![7, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN166 : N k166 = x2TrialForm 1 k166) (hN167 : N k167 = x2TrialForm 1 k167) (hN168 : N k168 = x2TrialForm 1 k168) :
    ∀ e ∈ ks, keyOK (x2Mult 1 7 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 1 N k166 4 _ gj288 x2Trial_288 v288 (by decide) (by rw [hN166]; exact trialForm_eq 1 k166 4 x2Trial_288 (by decide) rfl) chk166
  · exact keyOK_of_trialChk 1 N k167 3 _ gj289 x2Trial_289 v289 (by decide) (by rw [hN167]; exact trialForm_eq 1 k167 3 x2Trial_289 (by decide) rfl) chk167
  · exact keyOK_of_trial2Chk 1 N k168 7 _ gj290 x2Trial_290 v290 p290 (by decide) (by rw [hN168]; exact trialForm_eq 1 k168 7 x2Trial_290 (by decide) rfl) chk168

end ThreeCopyQutritWerner.X2.InK1x777
