module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x167
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k71 : x2Key 1 := ⟨71, by decide⟩
x2_gj_cols gj193 193 1 1 6 7 256
theorem gjc71_0 : (List.range 34).all (fun d => gjCheck 256 1 1 6 7 2 17 6 (x2JCols 193 (0 + d)) (gj193.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok71 : ∀ d < x2KeySize 1 k71, gjCheck 256 1 (x2KeyTypes 1 k71 0) (x2KeyTypes 1 k71 1) (x2KeyTypes 1 k71 2) (x2KeyMult 1 k71 0) (x2KeyMult 1 k71 1) (x2KeyMult 1 k71 2) (x2JCols (x2KeyGlobal 1 k71) d) (gj193.getD d 0) = true := by
  have hr : x2KeySize 1 k71 = 34 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 6 7 2 17 6 (x2JCols 193 d) (gj193.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 6 7 2 17 6 (x2JCols 193 d) (gj193.getD d 0)) 0 34 gjc71_0 d (Nat.zero_le d) (by omega)
x2_v_cols v193 gj193 193 256 204
theorem vc71_0 : (List.range 13).all (fun c => vCheck 256 204 34 gj193 (x2Trial_193.getD (0 + c) 0) (v193.getD (0 + c) 0)) = true := by decide +kernel
theorem vok71 : ∀ c < 13, vCheck 256 (x2KeyMult 1 k71 0 * x2KeyMult 1 k71 1 * x2KeyMult 1 k71 2) (x2KeySize 1 k71) gj193 (x2Trial_193.getD c 0) (v193.getD c 0) = true := by
  intro c hc
  show vCheck 256 204 34 gj193 (x2Trial_193.getD c 0) (v193.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 204 34 gj193 (x2Trial_193.getD c 0) (v193.getD c 0)) 0 13 vc71_0 c (Nat.zero_le c) (by omega)
theorem small71 : x2KeyDegree 1 k71 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k71 0 ∧ 1 ≤ x2KeyMult 1 k71 1 ∧ 1 ≤ x2KeyMult 1 k71 2 ∧ glRowOK 1 (x2KeyTypes 1 k71 0) (x2KeyMult 1 k71 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k71 1) (x2KeyMult 1 k71 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k71 2) (x2KeyMult 1 k71 2) 512 = true ∧ gj193.length = x2KeySize 1 k71 ∧ x2KeySize 1 k71 ≤ 512 ∧ v193.length = 13 := by decide +kernel
theorem chk71 : trialKeyChk 1 k71 13 gj193 x2Trial_193 v193 :=
  trialKeyChk_intro 1 k71 13 gj193 x2Trial_193 v193 small71 gjok71 vok71

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k71, ibFS [(v193, v193, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN71 : N k71 = x2TrialForm 1 k71) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k71 13 _ gj193 x2Trial_193 v193 (by decide) (by rw [hN71]; exact trialForm_eq 1 k71 13 x2Trial_193 (by decide) rfl) chk71

end ThreeCopyQutritWerner.X2.InK1x167
