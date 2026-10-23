module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x066
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k26 : x2Key 2 := ⟨26, by decide⟩
x2_gj_cols gj317 317 2 0 6 6 256
theorem gjc26_0 : (List.range 7).all (fun d => gjCheck 256 2 0 6 6 1 11 11 (x2JCols 317 (0 + d)) (gj317.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok26 : ∀ d < x2KeySize 2 k26, gjCheck 256 2 (x2KeyTypes 2 k26 0) (x2KeyTypes 2 k26 1) (x2KeyTypes 2 k26 2) (x2KeyMult 2 k26 0) (x2KeyMult 2 k26 1) (x2KeyMult 2 k26 2) (x2JCols (x2KeyGlobal 2 k26) d) (gj317.getD d 0) = true := by
  have hr : x2KeySize 2 k26 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 6 6 1 11 11 (x2JCols 317 d) (gj317.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 6 6 1 11 11 (x2JCols 317 d) (gj317.getD d 0)) 0 7 gjc26_0 d (Nat.zero_le d) (by omega)
x2_v_cols v317 gj317 317 256 121
theorem vc26_0 : (List.range 7).all (fun c => vCheck 256 121 7 gj317 (x2Trial_317.getD (0 + c) 0) (v317.getD (0 + c) 0)) = true := by decide +kernel
theorem vok26 : ∀ c < 7, vCheck 256 (x2KeyMult 2 k26 0 * x2KeyMult 2 k26 1 * x2KeyMult 2 k26 2) (x2KeySize 2 k26) gj317 (x2Trial_317.getD c 0) (v317.getD c 0) = true := by
  intro c hc
  show vCheck 256 121 7 gj317 (x2Trial_317.getD c 0) (v317.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 121 7 gj317 (x2Trial_317.getD c 0) (v317.getD c 0)) 0 7 vc26_0 c (Nat.zero_le c) (by omega)
theorem small26 : x2KeyDegree 2 k26 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k26 0 ∧ 1 ≤ x2KeyMult 2 k26 1 ∧ 1 ≤ x2KeyMult 2 k26 2 ∧ glRowOK 2 (x2KeyTypes 2 k26 0) (x2KeyMult 2 k26 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k26 1) (x2KeyMult 2 k26 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k26 2) (x2KeyMult 2 k26 2) 512 = true ∧ gj317.length = x2KeySize 2 k26 ∧ x2KeySize 2 k26 ≤ 512 ∧ v317.length = 7 := by decide +kernel
theorem chk26 : trialKeyChk 2 k26 7 gj317 x2Trial_317 v317 :=
  trialKeyChk_intro 2 k26 7 gj317 x2Trial_317 v317 small26 gjok26 vok26
def k27 : x2Key 2 := ⟨27, by decide⟩
x2_gj_cols gj318 318 2 0 6 6 256
theorem gjc27_0 : (List.range 3).all (fun d => gjCheck 256 2 0 6 6 1 11 11 (x2JCols 318 (0 + d)) (gj318.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok27 : ∀ d < x2KeySize 2 k27, gjCheck 256 2 (x2KeyTypes 2 k27 0) (x2KeyTypes 2 k27 1) (x2KeyTypes 2 k27 2) (x2KeyMult 2 k27 0) (x2KeyMult 2 k27 1) (x2KeyMult 2 k27 2) (x2JCols (x2KeyGlobal 2 k27) d) (gj318.getD d 0) = true := by
  have hr : x2KeySize 2 k27 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 6 6 1 11 11 (x2JCols 318 d) (gj318.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 6 6 1 11 11 (x2JCols 318 d) (gj318.getD d 0)) 0 3 gjc27_0 d (Nat.zero_le d) (by omega)
x2_v_cols v318 gj318 318 256 121
theorem vc27_0 : (List.range 3).all (fun c => vCheck 256 121 3 gj318 (x2Trial_318.getD (0 + c) 0) (v318.getD (0 + c) 0)) = true := by decide +kernel
theorem vok27 : ∀ c < 3, vCheck 256 (x2KeyMult 2 k27 0 * x2KeyMult 2 k27 1 * x2KeyMult 2 k27 2) (x2KeySize 2 k27) gj318 (x2Trial_318.getD c 0) (v318.getD c 0) = true := by
  intro c hc
  show vCheck 256 121 3 gj318 (x2Trial_318.getD c 0) (v318.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 121 3 gj318 (x2Trial_318.getD c 0) (v318.getD c 0)) 0 3 vc27_0 c (Nat.zero_le c) (by omega)
theorem small27 : x2KeyDegree 2 k27 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k27 0 ∧ 1 ≤ x2KeyMult 2 k27 1 ∧ 1 ≤ x2KeyMult 2 k27 2 ∧ glRowOK 2 (x2KeyTypes 2 k27 0) (x2KeyMult 2 k27 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k27 1) (x2KeyMult 2 k27 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k27 2) (x2KeyMult 2 k27 2) 512 = true ∧ gj318.length = x2KeySize 2 k27 ∧ x2KeySize 2 k27 ≤ 512 ∧ v318.length = 3 := by decide +kernel
theorem chk27 : trialKeyChk 2 k27 3 gj318 x2Trial_318 v318 :=
  trialKeyChk_intro 2 k27 3 gj318 x2Trial_318 v318 small27 gjok27 vok27

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k26, ibFS [(v317, v317, 94810963968000)]), (k27, ibFS [(v318, v318, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN26 : N k26 = x2TrialForm 2 k26) (hN27 : N k27 = x2TrialForm 2 k27) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k26 7 _ gj317 x2Trial_317 v317 (by decide) (by rw [hN26]; exact trialForm_eq 2 k26 7 x2Trial_317 (by decide) rfl) chk26
  · exact keyOK_of_trialChk 2 N k27 3 _ gj318 x2Trial_318 v318 (by decide) (by rw [hN27]; exact trialForm_eq 2 k27 3 x2Trial_318 (by decide) rfl) chk27

end ThreeCopyQutritWerner.X2.InK2x066
