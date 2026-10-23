module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x337
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k113 : x2Key 1 := ⟨113, by decide⟩
x2_gj_cols gj235 235 1 3 3 7 256
theorem gjc113_0 : (List.range 45).all (fun d => gjCheck 256 1 3 3 7 9 9 6 (x2JCols 235 (0 + d)) (gj235.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok113 : ∀ d < x2KeySize 1 k113, gjCheck 256 1 (x2KeyTypes 1 k113 0) (x2KeyTypes 1 k113 1) (x2KeyTypes 1 k113 2) (x2KeyMult 1 k113 0) (x2KeyMult 1 k113 1) (x2KeyMult 1 k113 2) (x2JCols (x2KeyGlobal 1 k113) d) (gj235.getD d 0) = true := by
  have hr : x2KeySize 1 k113 = 45 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 7 9 9 6 (x2JCols 235 d) (gj235.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 7 9 9 6 (x2JCols 235 d) (gj235.getD d 0)) 0 45 gjc113_0 d (Nat.zero_le d) (by omega)
x2_v_cols v235 gj235 235 256 486
theorem vc113_0 : (List.range 15).all (fun c => vCheck 256 486 45 gj235 (x2Trial_235.getD (0 + c) 0) (v235.getD (0 + c) 0)) = true := by decide +kernel
theorem vok113 : ∀ c < 15, vCheck 256 (x2KeyMult 1 k113 0 * x2KeyMult 1 k113 1 * x2KeyMult 1 k113 2) (x2KeySize 1 k113) gj235 (x2Trial_235.getD c 0) (v235.getD c 0) = true := by
  intro c hc
  show vCheck 256 486 45 gj235 (x2Trial_235.getD c 0) (v235.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 486 45 gj235 (x2Trial_235.getD c 0) (v235.getD c 0)) 0 15 vc113_0 c (Nat.zero_le c) (by omega)
theorem small113 : x2KeyDegree 1 k113 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k113 0 ∧ 1 ≤ x2KeyMult 1 k113 1 ∧ 1 ≤ x2KeyMult 1 k113 2 ∧ glRowOK 1 (x2KeyTypes 1 k113 0) (x2KeyMult 1 k113 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k113 1) (x2KeyMult 1 k113 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k113 2) (x2KeyMult 1 k113 2) 512 = true ∧ gj235.length = x2KeySize 1 k113 ∧ x2KeySize 1 k113 ≤ 512 ∧ v235.length = 15 := by decide +kernel
theorem chk113 : trialKeyChk 1 k113 15 gj235 x2Trial_235 v235 :=
  trialKeyChk_intro 1 k113 15 gj235 x2Trial_235 v235 small113 gjok113 vok113
def k114 : x2Key 1 := ⟨114, by decide⟩
x2_gj_cols gj236 236 1 3 3 7 256
theorem gjc114_0 : (List.range 36).all (fun d => gjCheck 256 1 3 3 7 9 9 6 (x2JCols 236 (0 + d)) (gj236.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok114 : ∀ d < x2KeySize 1 k114, gjCheck 256 1 (x2KeyTypes 1 k114 0) (x2KeyTypes 1 k114 1) (x2KeyTypes 1 k114 2) (x2KeyMult 1 k114 0) (x2KeyMult 1 k114 1) (x2KeyMult 1 k114 2) (x2JCols (x2KeyGlobal 1 k114) d) (gj236.getD d 0) = true := by
  have hr : x2KeySize 1 k114 = 36 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 7 9 9 6 (x2JCols 236 d) (gj236.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 7 9 9 6 (x2JCols 236 d) (gj236.getD d 0)) 0 36 gjc114_0 d (Nat.zero_le d) (by omega)
x2_v_cols v236 gj236 236 256 486
theorem vc114_0 : (List.range 13).all (fun c => vCheck 256 486 36 gj236 (x2Trial_236.getD (0 + c) 0) (v236.getD (0 + c) 0)) = true := by decide +kernel
theorem vok114 : ∀ c < 13, vCheck 256 (x2KeyMult 1 k114 0 * x2KeyMult 1 k114 1 * x2KeyMult 1 k114 2) (x2KeySize 1 k114) gj236 (x2Trial_236.getD c 0) (v236.getD c 0) = true := by
  intro c hc
  show vCheck 256 486 36 gj236 (x2Trial_236.getD c 0) (v236.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 486 36 gj236 (x2Trial_236.getD c 0) (v236.getD c 0)) 0 13 vc114_0 c (Nat.zero_le c) (by omega)
theorem small114 : x2KeyDegree 1 k114 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k114 0 ∧ 1 ≤ x2KeyMult 1 k114 1 ∧ 1 ≤ x2KeyMult 1 k114 2 ∧ glRowOK 1 (x2KeyTypes 1 k114 0) (x2KeyMult 1 k114 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k114 1) (x2KeyMult 1 k114 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k114 2) (x2KeyMult 1 k114 2) 512 = true ∧ gj236.length = x2KeySize 1 k114 ∧ x2KeySize 1 k114 ≤ 512 ∧ v236.length = 13 := by decide +kernel
theorem chk114 : trialKeyChk 1 k114 13 gj236 x2Trial_236 v236 :=
  trialKeyChk_intro 1 k114 13 gj236 x2Trial_236 v236 small114 gjok114 vok114

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k113, ibFS [(v235, v235, 94810963968000)]), (k114, ibFS [(v236, v236, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 3, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN113 : N k113 = x2TrialForm 1 k113) (hN114 : N k114 = x2TrialForm 1 k114) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 3 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k113 15 _ gj235 x2Trial_235 v235 (by decide) (by rw [hN113]; exact trialForm_eq 1 k113 15 x2Trial_235 (by decide) rfl) chk113
  · exact keyOK_of_trialChk 1 N k114 13 _ gj236 x2Trial_236 v236 (by decide) (by rw [hN114]; exact trialForm_eq 1 k114 13 x2Trial_236 (by decide) rfl) chk114

end ThreeCopyQutritWerner.X2.InK1x337
