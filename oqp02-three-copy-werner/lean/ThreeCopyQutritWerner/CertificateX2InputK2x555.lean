module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x555
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k113 : x2Key 2 := ⟨113, by decide⟩
x2_gj_cols gj404 404 2 5 5 5 256
theorem gjc113_0 : (List.range 20).all (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 404 (0 + d)) (gj404.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok113 : ∀ d < x2KeySize 2 k113, gjCheck 256 2 (x2KeyTypes 2 k113 0) (x2KeyTypes 2 k113 1) (x2KeyTypes 2 k113 2) (x2KeyMult 2 k113 0) (x2KeyMult 2 k113 1) (x2KeyMult 2 k113 2) (x2JCols (x2KeyGlobal 2 k113) d) (gj404.getD d 0) = true := by
  have hr : x2KeySize 2 k113 = 20 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 5 5 10 10 10 (x2JCols 404 d) (gj404.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 404 d) (gj404.getD d 0)) 0 20 gjc113_0 d (Nat.zero_le d) (by omega)
x2_v_cols v404 gj404 404 256 1000
theorem vc113_0 : (List.range 14).all (fun c => vCheck 256 1000 20 gj404 (x2Trial_404.getD (0 + c) 0) (v404.getD (0 + c) 0)) = true := by decide +kernel
theorem vok113 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k113 0 * x2KeyMult 2 k113 1 * x2KeyMult 2 k113 2) (x2KeySize 2 k113) gj404 (x2Trial_404.getD c 0) (v404.getD c 0) = true := by
  intro c hc
  show vCheck 256 1000 20 gj404 (x2Trial_404.getD c 0) (v404.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1000 20 gj404 (x2Trial_404.getD c 0) (v404.getD c 0)) 0 14 vc113_0 c (Nat.zero_le c) (by omega)
theorem small113 : x2KeyDegree 2 k113 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k113 0 ∧ 1 ≤ x2KeyMult 2 k113 1 ∧ 1 ≤ x2KeyMult 2 k113 2 ∧ glRowOK 2 (x2KeyTypes 2 k113 0) (x2KeyMult 2 k113 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k113 1) (x2KeyMult 2 k113 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k113 2) (x2KeyMult 2 k113 2) 512 = true ∧ gj404.length = x2KeySize 2 k113 ∧ x2KeySize 2 k113 ≤ 512 ∧ v404.length = 14 := by decide +kernel
theorem chk113 : trialKeyChk 2 k113 14 gj404 x2Trial_404 v404 :=
  trialKeyChk_intro 2 k113 14 gj404 x2Trial_404 v404 small113 gjok113 vok113
def k114 : x2Key 2 := ⟨114, by decide⟩
x2_gj_cols gj405 405 2 5 5 5 256
theorem gjc114_0 : (List.range 8).all (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 405 (0 + d)) (gj405.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok114 : ∀ d < x2KeySize 2 k114, gjCheck 256 2 (x2KeyTypes 2 k114 0) (x2KeyTypes 2 k114 1) (x2KeyTypes 2 k114 2) (x2KeyMult 2 k114 0) (x2KeyMult 2 k114 1) (x2KeyMult 2 k114 2) (x2JCols (x2KeyGlobal 2 k114) d) (gj405.getD d 0) = true := by
  have hr : x2KeySize 2 k114 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 5 5 10 10 10 (x2JCols 405 d) (gj405.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 405 d) (gj405.getD d 0)) 0 8 gjc114_0 d (Nat.zero_le d) (by omega)
x2_v_cols v405 gj405 405 256 1000
theorem vc114_0 : (List.range 7).all (fun c => vCheck 256 1000 8 gj405 (x2Trial_405.getD (0 + c) 0) (v405.getD (0 + c) 0)) = true := by decide +kernel
theorem vok114 : ∀ c < 7, vCheck 256 (x2KeyMult 2 k114 0 * x2KeyMult 2 k114 1 * x2KeyMult 2 k114 2) (x2KeySize 2 k114) gj405 (x2Trial_405.getD c 0) (v405.getD c 0) = true := by
  intro c hc
  show vCheck 256 1000 8 gj405 (x2Trial_405.getD c 0) (v405.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1000 8 gj405 (x2Trial_405.getD c 0) (v405.getD c 0)) 0 7 vc114_0 c (Nat.zero_le c) (by omega)
theorem small114 : x2KeyDegree 2 k114 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k114 0 ∧ 1 ≤ x2KeyMult 2 k114 1 ∧ 1 ≤ x2KeyMult 2 k114 2 ∧ glRowOK 2 (x2KeyTypes 2 k114 0) (x2KeyMult 2 k114 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k114 1) (x2KeyMult 2 k114 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k114 2) (x2KeyMult 2 k114 2) 512 = true ∧ gj405.length = x2KeySize 2 k114 ∧ x2KeySize 2 k114 ≤ 512 ∧ v405.length = 7 := by decide +kernel
theorem chk114 : trialKeyChk 2 k114 7 gj405 x2Trial_405 v405 :=
  trialKeyChk_intro 2 k114 7 gj405 x2Trial_405 v405 small114 gjok114 vok114
def k115 : x2Key 2 := ⟨115, by decide⟩
x2_gj_cols gj406 406 2 5 5 5 256
theorem gjc115_0 : (List.range 30).all (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 406 (0 + d)) (gj406.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok115 : ∀ d < x2KeySize 2 k115, gjCheck 256 2 (x2KeyTypes 2 k115 0) (x2KeyTypes 2 k115 1) (x2KeyTypes 2 k115 2) (x2KeyMult 2 k115 0) (x2KeyMult 2 k115 1) (x2KeyMult 2 k115 2) (x2JCols (x2KeyGlobal 2 k115) d) (gj406.getD d 0) = true := by
  have hr : x2KeySize 2 k115 = 30 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 5 5 10 10 10 (x2JCols 406 d) (gj406.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 5 5 10 10 10 (x2JCols 406 d) (gj406.getD d 0)) 0 30 gjc115_0 d (Nat.zero_le d) (by omega)
x2_v_cols v406 gj406 406 256 1000
theorem vc115_0 : (List.range 23).all (fun c => vCheck 256 1000 30 gj406 (x2Trial_406.getD (0 + c) 0) (v406.getD (0 + c) 0)) = true := by decide +kernel
theorem vok115 : ∀ c < 23, vCheck 256 (x2KeyMult 2 k115 0 * x2KeyMult 2 k115 1 * x2KeyMult 2 k115 2) (x2KeySize 2 k115) gj406 (x2Trial_406.getD c 0) (v406.getD c 0) = true := by
  intro c hc
  show vCheck 256 1000 30 gj406 (x2Trial_406.getD c 0) (v406.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1000 30 gj406 (x2Trial_406.getD c 0) (v406.getD c 0)) 0 23 vc115_0 c (Nat.zero_le c) (by omega)
x2_p_cols p406 v406 10
theorem pok115 : ∀ c < 23, partnerCheck (x2KeyMult 2 k115 0) (v406.getD c 0) (p406.getD c 0) = true := by
  intro c hc
  show partnerCheck 10 (v406.getD c 0) (p406.getD c 0) = true
  have h : (List.range 23).all (fun c => partnerCheck 10 (v406.getD c 0) (p406.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small115 : x2KeyDegree 2 k115 = 2 ∧ x2KeyMult 2 k115 0 = x2KeyMult 2 k115 1 ∧ x2KeyMult 2 k115 1 = x2KeyMult 2 k115 2 ∧ 1 ≤ x2KeyMult 2 k115 0 ∧ glRowOK 2 (x2KeyTypes 2 k115 0) (x2KeyMult 2 k115 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k115 1) (x2KeyMult 2 k115 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k115 2) (x2KeyMult 2 k115 2) 512 = true ∧ gj406.length = x2KeySize 2 k115 ∧ x2KeySize 2 k115 ≤ 512 ∧ v406.length = 23 ∧ p406.length = 23 := by decide +kernel
theorem chk115 : trial2KeyChk 2 k115 23 gj406 x2Trial_406 v406 p406 :=
  trial2KeyChk_intro 2 k115 23 gj406 x2Trial_406 v406 p406 small115 gjok115 vok115 pok115

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k113, ibFS [(v404, v404, 94810963968000)]), (k114, ibFS [(v405, v405, 94810963968000)]), (k115, ibFS [(v406, v406, 94810963968000), (p406, p406, 31603654656000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![5, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN113 : N k113 = x2TrialForm 2 k113) (hN114 : N k114 = x2TrialForm 2 k114) (hN115 : N k115 = x2TrialForm 2 k115) :
    ∀ e ∈ ks, keyOK (x2Mult 2 5 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 2 N k113 14 _ gj404 x2Trial_404 v404 (by decide) (by rw [hN113]; exact trialForm_eq 2 k113 14 x2Trial_404 (by decide) rfl) chk113
  · exact keyOK_of_trialChk 2 N k114 7 _ gj405 x2Trial_405 v405 (by decide) (by rw [hN114]; exact trialForm_eq 2 k114 7 x2Trial_405 (by decide) rfl) chk114
  · exact keyOK_of_trial2Chk 2 N k115 23 _ gj406 x2Trial_406 v406 p406 (by decide) (by rw [hN115]; exact trialForm_eq 2 k115 23 x2Trial_406 (by decide) rfl) chk115

end ThreeCopyQutritWerner.X2.InK2x555
