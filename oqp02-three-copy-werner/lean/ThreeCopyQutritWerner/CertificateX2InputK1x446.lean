module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x446
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k134 : x2Key 1 := ⟨134, by decide⟩
x2_gj_cols gj256 256 1 4 4 6 256
theorem gjc134_0 : (List.range 79).all (fun d => gjCheck 256 1 4 4 6 7 7 17 (x2JCols 256 (0 + d)) (gj256.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok134 : ∀ d < x2KeySize 1 k134, gjCheck 256 1 (x2KeyTypes 1 k134 0) (x2KeyTypes 1 k134 1) (x2KeyTypes 1 k134 2) (x2KeyMult 1 k134 0) (x2KeyMult 1 k134 1) (x2KeyMult 1 k134 2) (x2JCols (x2KeyGlobal 1 k134) d) (gj256.getD d 0) = true := by
  have hr : x2KeySize 1 k134 = 79 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 6 7 7 17 (x2JCols 256 d) (gj256.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 6 7 7 17 (x2JCols 256 d) (gj256.getD d 0)) 0 79 gjc134_0 d (Nat.zero_le d) (by omega)
x2_v_cols v256 gj256 256 256 833
theorem vc134_0 : (List.range 51).all (fun c => vCheck 256 833 79 gj256 (x2Trial_256.getD (0 + c) 0) (v256.getD (0 + c) 0)) = true := by decide +kernel
theorem vok134 : ∀ c < 51, vCheck 256 (x2KeyMult 1 k134 0 * x2KeyMult 1 k134 1 * x2KeyMult 1 k134 2) (x2KeySize 1 k134) gj256 (x2Trial_256.getD c 0) (v256.getD c 0) = true := by
  intro c hc
  show vCheck 256 833 79 gj256 (x2Trial_256.getD c 0) (v256.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 833 79 gj256 (x2Trial_256.getD c 0) (v256.getD c 0)) 0 51 vc134_0 c (Nat.zero_le c) (by omega)
theorem small134 : x2KeyDegree 1 k134 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k134 0 ∧ 1 ≤ x2KeyMult 1 k134 1 ∧ 1 ≤ x2KeyMult 1 k134 2 ∧ glRowOK 1 (x2KeyTypes 1 k134 0) (x2KeyMult 1 k134 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k134 1) (x2KeyMult 1 k134 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k134 2) (x2KeyMult 1 k134 2) 512 = true ∧ gj256.length = x2KeySize 1 k134 ∧ x2KeySize 1 k134 ≤ 512 ∧ v256.length = 51 := by decide +kernel
theorem chk134 : trialKeyChk 1 k134 51 gj256 x2Trial_256 v256 :=
  trialKeyChk_intro 1 k134 51 gj256 x2Trial_256 v256 small134 gjok134 vok134
def k135 : x2Key 1 := ⟨135, by decide⟩
x2_gj_cols gj257 257 1 4 4 6 256
theorem gjc135_0 : (List.range 60).all (fun d => gjCheck 256 1 4 4 6 7 7 17 (x2JCols 257 (0 + d)) (gj257.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok135 : ∀ d < x2KeySize 1 k135, gjCheck 256 1 (x2KeyTypes 1 k135 0) (x2KeyTypes 1 k135 1) (x2KeyTypes 1 k135 2) (x2KeyMult 1 k135 0) (x2KeyMult 1 k135 1) (x2KeyMult 1 k135 2) (x2JCols (x2KeyGlobal 1 k135) d) (gj257.getD d 0) = true := by
  have hr : x2KeySize 1 k135 = 60 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 6 7 7 17 (x2JCols 257 d) (gj257.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 6 7 7 17 (x2JCols 257 d) (gj257.getD d 0)) 0 60 gjc135_0 d (Nat.zero_le d) (by omega)
x2_v_cols v257 gj257 257 256 833
theorem vc135_0 : (List.range 39).all (fun c => vCheck 256 833 60 gj257 (x2Trial_257.getD (0 + c) 0) (v257.getD (0 + c) 0)) = true := by decide +kernel
theorem vok135 : ∀ c < 39, vCheck 256 (x2KeyMult 1 k135 0 * x2KeyMult 1 k135 1 * x2KeyMult 1 k135 2) (x2KeySize 1 k135) gj257 (x2Trial_257.getD c 0) (v257.getD c 0) = true := by
  intro c hc
  show vCheck 256 833 60 gj257 (x2Trial_257.getD c 0) (v257.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 833 60 gj257 (x2Trial_257.getD c 0) (v257.getD c 0)) 0 39 vc135_0 c (Nat.zero_le c) (by omega)
theorem small135 : x2KeyDegree 1 k135 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k135 0 ∧ 1 ≤ x2KeyMult 1 k135 1 ∧ 1 ≤ x2KeyMult 1 k135 2 ∧ glRowOK 1 (x2KeyTypes 1 k135 0) (x2KeyMult 1 k135 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k135 1) (x2KeyMult 1 k135 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k135 2) (x2KeyMult 1 k135 2) 512 = true ∧ gj257.length = x2KeySize 1 k135 ∧ x2KeySize 1 k135 ≤ 512 ∧ v257.length = 39 := by decide +kernel
theorem chk135 : trialKeyChk 1 k135 39 gj257 x2Trial_257 v257 :=
  trialKeyChk_intro 1 k135 39 gj257 x2Trial_257 v257 small135 gjok135 vok135

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k134, ibFS [(v256, v256, 94810963968000)]), (k135, ibFS [(v257, v257, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN134 : N k134 = x2TrialForm 1 k134) (hN135 : N k135 = x2TrialForm 1 k135) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 4 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k134 51 _ gj256 x2Trial_256 v256 (by decide) (by rw [hN134]; exact trialForm_eq 1 k134 51 x2Trial_256 (by decide) rfl) chk134
  · exact keyOK_of_trialChk 1 N k135 39 _ gj257 x2Trial_257 v257 (by decide) (by rw [hN135]; exact trialForm_eq 1 k135 39 x2Trial_257 (by decide) rfl) chk135

end ThreeCopyQutritWerner.X2.InK1x446
