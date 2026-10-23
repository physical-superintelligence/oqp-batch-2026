module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x255
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k79 : x2Key 2 := ⟨79, by decide⟩
x2_gj_cols gj370 370 2 2 5 5 256
theorem gjc79_0 : (List.range 24).all (fun d => gjCheck 256 2 2 5 5 5 10 10 (x2JCols 370 (0 + d)) (gj370.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok79 : ∀ d < x2KeySize 2 k79, gjCheck 256 2 (x2KeyTypes 2 k79 0) (x2KeyTypes 2 k79 1) (x2KeyTypes 2 k79 2) (x2KeyMult 2 k79 0) (x2KeyMult 2 k79 1) (x2KeyMult 2 k79 2) (x2JCols (x2KeyGlobal 2 k79) d) (gj370.getD d 0) = true := by
  have hr : x2KeySize 2 k79 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 5 5 5 10 10 (x2JCols 370 d) (gj370.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 5 5 5 10 10 (x2JCols 370 d) (gj370.getD d 0)) 0 24 gjc79_0 d (Nat.zero_le d) (by omega)
x2_v_cols v370 gj370 370 256 500
theorem vc79_0 : (List.range 20).all (fun c => vCheck 256 500 24 gj370 (x2Trial_370.getD (0 + c) 0) (v370.getD (0 + c) 0)) = true := by decide +kernel
theorem vok79 : ∀ c < 20, vCheck 256 (x2KeyMult 2 k79 0 * x2KeyMult 2 k79 1 * x2KeyMult 2 k79 2) (x2KeySize 2 k79) gj370 (x2Trial_370.getD c 0) (v370.getD c 0) = true := by
  intro c hc
  show vCheck 256 500 24 gj370 (x2Trial_370.getD c 0) (v370.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 500 24 gj370 (x2Trial_370.getD c 0) (v370.getD c 0)) 0 20 vc79_0 c (Nat.zero_le c) (by omega)
theorem small79 : x2KeyDegree 2 k79 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k79 0 ∧ 1 ≤ x2KeyMult 2 k79 1 ∧ 1 ≤ x2KeyMult 2 k79 2 ∧ glRowOK 2 (x2KeyTypes 2 k79 0) (x2KeyMult 2 k79 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k79 1) (x2KeyMult 2 k79 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k79 2) (x2KeyMult 2 k79 2) 512 = true ∧ gj370.length = x2KeySize 2 k79 ∧ x2KeySize 2 k79 ≤ 512 ∧ v370.length = 20 := by decide +kernel
theorem chk79 : trialKeyChk 2 k79 20 gj370 x2Trial_370 v370 :=
  trialKeyChk_intro 2 k79 20 gj370 x2Trial_370 v370 small79 gjok79 vok79
def k80 : x2Key 2 := ⟨80, by decide⟩
x2_gj_cols gj371 371 2 2 5 5 256
theorem gjc80_0 : (List.range 16).all (fun d => gjCheck 256 2 2 5 5 5 10 10 (x2JCols 371 (0 + d)) (gj371.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok80 : ∀ d < x2KeySize 2 k80, gjCheck 256 2 (x2KeyTypes 2 k80 0) (x2KeyTypes 2 k80 1) (x2KeyTypes 2 k80 2) (x2KeyMult 2 k80 0) (x2KeyMult 2 k80 1) (x2KeyMult 2 k80 2) (x2JCols (x2KeyGlobal 2 k80) d) (gj371.getD d 0) = true := by
  have hr : x2KeySize 2 k80 = 16 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 5 5 5 10 10 (x2JCols 371 d) (gj371.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 5 5 5 10 10 (x2JCols 371 d) (gj371.getD d 0)) 0 16 gjc80_0 d (Nat.zero_le d) (by omega)
x2_v_cols v371 gj371 371 256 500
theorem vc80_0 : (List.range 14).all (fun c => vCheck 256 500 16 gj371 (x2Trial_371.getD (0 + c) 0) (v371.getD (0 + c) 0)) = true := by decide +kernel
theorem vok80 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k80 0 * x2KeyMult 2 k80 1 * x2KeyMult 2 k80 2) (x2KeySize 2 k80) gj371 (x2Trial_371.getD c 0) (v371.getD c 0) = true := by
  intro c hc
  show vCheck 256 500 16 gj371 (x2Trial_371.getD c 0) (v371.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 500 16 gj371 (x2Trial_371.getD c 0) (v371.getD c 0)) 0 14 vc80_0 c (Nat.zero_le c) (by omega)
theorem small80 : x2KeyDegree 2 k80 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k80 0 ∧ 1 ≤ x2KeyMult 2 k80 1 ∧ 1 ≤ x2KeyMult 2 k80 2 ∧ glRowOK 2 (x2KeyTypes 2 k80 0) (x2KeyMult 2 k80 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k80 1) (x2KeyMult 2 k80 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k80 2) (x2KeyMult 2 k80 2) 512 = true ∧ gj371.length = x2KeySize 2 k80 ∧ x2KeySize 2 k80 ≤ 512 ∧ v371.length = 14 := by decide +kernel
theorem chk80 : trialKeyChk 2 k80 14 gj371 x2Trial_371 v371 :=
  trialKeyChk_intro 2 k80 14 gj371 x2Trial_371 v371 small80 gjok80 vok80

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k79, ibFS [(v370, v370, 94810963968000)]), (k80, ibFS [(v371, v371, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN79 : N k79 = x2TrialForm 2 k79) (hN80 : N k80 = x2TrialForm 2 k80) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k79 20 _ gj370 x2Trial_370 v370 (by decide) (by rw [hN79]; exact trialForm_eq 2 k79 20 x2Trial_370 (by decide) rfl) chk79
  · exact keyOK_of_trialChk 2 N k80 14 _ gj371 x2Trial_371 v371 (by decide) (by rw [hN80]; exact trialForm_eq 2 k80 14 x2Trial_371 (by decide) rfl) chk80

end ThreeCopyQutritWerner.X2.InK2x255
