module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x377
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k127 : x2Key 1 := ⟨127, by decide⟩
x2_gj_cols gj249 249 1 3 7 7 256
theorem gjc127_0 : (List.range 30).all (fun d => gjCheck 256 1 3 7 7 9 6 6 (x2JCols 249 (0 + d)) (gj249.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok127 : ∀ d < x2KeySize 1 k127, gjCheck 256 1 (x2KeyTypes 1 k127 0) (x2KeyTypes 1 k127 1) (x2KeyTypes 1 k127 2) (x2KeyMult 1 k127 0) (x2KeyMult 1 k127 1) (x2KeyMult 1 k127 2) (x2JCols (x2KeyGlobal 1 k127) d) (gj249.getD d 0) = true := by
  have hr : x2KeySize 1 k127 = 30 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 7 7 9 6 6 (x2JCols 249 d) (gj249.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 7 7 9 6 6 (x2JCols 249 d) (gj249.getD d 0)) 0 30 gjc127_0 d (Nat.zero_le d) (by omega)
x2_v_cols v249 gj249 249 256 324
theorem vc127_0 : (List.range 14).all (fun c => vCheck 256 324 30 gj249 (x2Trial_249.getD (0 + c) 0) (v249.getD (0 + c) 0)) = true := by decide +kernel
theorem vok127 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k127 0 * x2KeyMult 1 k127 1 * x2KeyMult 1 k127 2) (x2KeySize 1 k127) gj249 (x2Trial_249.getD c 0) (v249.getD c 0) = true := by
  intro c hc
  show vCheck 256 324 30 gj249 (x2Trial_249.getD c 0) (v249.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 324 30 gj249 (x2Trial_249.getD c 0) (v249.getD c 0)) 0 14 vc127_0 c (Nat.zero_le c) (by omega)
theorem small127 : x2KeyDegree 1 k127 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k127 0 ∧ 1 ≤ x2KeyMult 1 k127 1 ∧ 1 ≤ x2KeyMult 1 k127 2 ∧ glRowOK 1 (x2KeyTypes 1 k127 0) (x2KeyMult 1 k127 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k127 1) (x2KeyMult 1 k127 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k127 2) (x2KeyMult 1 k127 2) 512 = true ∧ gj249.length = x2KeySize 1 k127 ∧ x2KeySize 1 k127 ≤ 512 ∧ v249.length = 14 := by decide +kernel
theorem chk127 : trialKeyChk 1 k127 14 gj249 x2Trial_249 v249 :=
  trialKeyChk_intro 1 k127 14 gj249 x2Trial_249 v249 small127 gjok127 vok127
def k128 : x2Key 1 := ⟨128, by decide⟩
x2_gj_cols gj250 250 1 3 7 7 256
theorem gjc128_0 : (List.range 24).all (fun d => gjCheck 256 1 3 7 7 9 6 6 (x2JCols 250 (0 + d)) (gj250.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok128 : ∀ d < x2KeySize 1 k128, gjCheck 256 1 (x2KeyTypes 1 k128 0) (x2KeyTypes 1 k128 1) (x2KeyTypes 1 k128 2) (x2KeyMult 1 k128 0) (x2KeyMult 1 k128 1) (x2KeyMult 1 k128 2) (x2JCols (x2KeyGlobal 1 k128) d) (gj250.getD d 0) = true := by
  have hr : x2KeySize 1 k128 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 7 7 9 6 6 (x2JCols 250 d) (gj250.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 7 7 9 6 6 (x2JCols 250 d) (gj250.getD d 0)) 0 24 gjc128_0 d (Nat.zero_le d) (by omega)
x2_v_cols v250 gj250 250 256 324
theorem vc128_0 : (List.range 14).all (fun c => vCheck 256 324 24 gj250 (x2Trial_250.getD (0 + c) 0) (v250.getD (0 + c) 0)) = true := by decide +kernel
theorem vok128 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k128 0 * x2KeyMult 1 k128 1 * x2KeyMult 1 k128 2) (x2KeySize 1 k128) gj250 (x2Trial_250.getD c 0) (v250.getD c 0) = true := by
  intro c hc
  show vCheck 256 324 24 gj250 (x2Trial_250.getD c 0) (v250.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 324 24 gj250 (x2Trial_250.getD c 0) (v250.getD c 0)) 0 14 vc128_0 c (Nat.zero_le c) (by omega)
theorem small128 : x2KeyDegree 1 k128 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k128 0 ∧ 1 ≤ x2KeyMult 1 k128 1 ∧ 1 ≤ x2KeyMult 1 k128 2 ∧ glRowOK 1 (x2KeyTypes 1 k128 0) (x2KeyMult 1 k128 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k128 1) (x2KeyMult 1 k128 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k128 2) (x2KeyMult 1 k128 2) 512 = true ∧ gj250.length = x2KeySize 1 k128 ∧ x2KeySize 1 k128 ≤ 512 ∧ v250.length = 14 := by decide +kernel
theorem chk128 : trialKeyChk 1 k128 14 gj250 x2Trial_250 v250 :=
  trialKeyChk_intro 1 k128 14 gj250 x2Trial_250 v250 small128 gjok128 vok128

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k127, ibFS [(v249, v249, 94810963968000)]), (k128, ibFS [(v250, v250, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN127 : N k127 = x2TrialForm 1 k127) (hN128 : N k128 = x2TrialForm 1 k128) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k127 14 _ gj249 x2Trial_249 v249 (by decide) (by rw [hN127]; exact trialForm_eq 1 k127 14 x2Trial_249 (by decide) rfl) chk127
  · exact keyOK_of_trialChk 1 N k128 14 _ gj250 x2Trial_250 v250 (by decide) (by rw [hN128]; exact trialForm_eq 1 k128 14 x2Trial_250 (by decide) rfl) chk128

end ThreeCopyQutritWerner.X2.InK1x377
