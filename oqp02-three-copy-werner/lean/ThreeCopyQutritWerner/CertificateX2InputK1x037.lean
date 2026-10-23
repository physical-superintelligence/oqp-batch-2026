module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x037
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k21 : x2Key 1 := ⟨21, by decide⟩
x2_gj_cols gj143 143 1 0 3 7 256
theorem gjc21_0 : (List.range 9).all (fun d => gjCheck 256 1 0 3 7 1 9 6 (x2JCols 143 (0 + d)) (gj143.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok21 : ∀ d < x2KeySize 1 k21, gjCheck 256 1 (x2KeyTypes 1 k21 0) (x2KeyTypes 1 k21 1) (x2KeyTypes 1 k21 2) (x2KeyMult 1 k21 0) (x2KeyMult 1 k21 1) (x2KeyMult 1 k21 2) (x2JCols (x2KeyGlobal 1 k21) d) (gj143.getD d 0) = true := by
  have hr : x2KeySize 1 k21 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 3 7 1 9 6 (x2JCols 143 d) (gj143.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 3 7 1 9 6 (x2JCols 143 d) (gj143.getD d 0)) 0 9 gjc21_0 d (Nat.zero_le d) (by omega)
x2_v_cols v143 gj143 143 256 54
theorem vc21_0 : (List.range 2).all (fun c => vCheck 256 54 9 gj143 (x2Trial_143.getD (0 + c) 0) (v143.getD (0 + c) 0)) = true := by decide +kernel
theorem vok21 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k21 0 * x2KeyMult 1 k21 1 * x2KeyMult 1 k21 2) (x2KeySize 1 k21) gj143 (x2Trial_143.getD c 0) (v143.getD c 0) = true := by
  intro c hc
  show vCheck 256 54 9 gj143 (x2Trial_143.getD c 0) (v143.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 54 9 gj143 (x2Trial_143.getD c 0) (v143.getD c 0)) 0 2 vc21_0 c (Nat.zero_le c) (by omega)
theorem small21 : x2KeyDegree 1 k21 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k21 0 ∧ 1 ≤ x2KeyMult 1 k21 1 ∧ 1 ≤ x2KeyMult 1 k21 2 ∧ glRowOK 1 (x2KeyTypes 1 k21 0) (x2KeyMult 1 k21 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k21 1) (x2KeyMult 1 k21 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k21 2) (x2KeyMult 1 k21 2) 512 = true ∧ gj143.length = x2KeySize 1 k21 ∧ x2KeySize 1 k21 ≤ 512 ∧ v143.length = 2 := by decide +kernel
theorem chk21 : trialKeyChk 1 k21 2 gj143 x2Trial_143 v143 :=
  trialKeyChk_intro 1 k21 2 gj143 x2Trial_143 v143 small21 gjok21 vok21

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k21, ibFS [(v143, v143, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 3, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN21 : N k21 = x2TrialForm 1 k21) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 3 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k21 2 _ gj143 x2Trial_143 v143 (by decide) (by rw [hN21]; exact trialForm_eq 1 k21 2 x2Trial_143 (by decide) rfl) chk21

end ThreeCopyQutritWerner.X2.InK1x037
