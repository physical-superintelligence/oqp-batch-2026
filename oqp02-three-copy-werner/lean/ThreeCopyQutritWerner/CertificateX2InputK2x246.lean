module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x246
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k78 : x2Key 2 := ⟨78, by decide⟩
x2_gj_cols gj369 369 2 2 4 6 256
theorem gjc78_0 : (List.range 69).all (fun d => gjCheck 256 2 2 4 6 5 15 11 (x2JCols 369 (0 + d)) (gj369.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok78 : ∀ d < x2KeySize 2 k78, gjCheck 256 2 (x2KeyTypes 2 k78 0) (x2KeyTypes 2 k78 1) (x2KeyTypes 2 k78 2) (x2KeyMult 2 k78 0) (x2KeyMult 2 k78 1) (x2KeyMult 2 k78 2) (x2JCols (x2KeyGlobal 2 k78) d) (gj369.getD d 0) = true := by
  have hr : x2KeySize 2 k78 = 69 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 4 6 5 15 11 (x2JCols 369 d) (gj369.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 4 6 5 15 11 (x2JCols 369 d) (gj369.getD d 0)) 0 69 gjc78_0 d (Nat.zero_le d) (by omega)
x2_v_cols v369 gj369 369 256 825
theorem vc78_0 : (List.range 69).all (fun c => vCheck 256 825 69 gj369 (x2Trial_369.getD (0 + c) 0) (v369.getD (0 + c) 0)) = true := by decide +kernel
theorem vok78 : ∀ c < 69, vCheck 256 (x2KeyMult 2 k78 0 * x2KeyMult 2 k78 1 * x2KeyMult 2 k78 2) (x2KeySize 2 k78) gj369 (x2Trial_369.getD c 0) (v369.getD c 0) = true := by
  intro c hc
  show vCheck 256 825 69 gj369 (x2Trial_369.getD c 0) (v369.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 825 69 gj369 (x2Trial_369.getD c 0) (v369.getD c 0)) 0 69 vc78_0 c (Nat.zero_le c) (by omega)
theorem small78 : x2KeyDegree 2 k78 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k78 0 ∧ 1 ≤ x2KeyMult 2 k78 1 ∧ 1 ≤ x2KeyMult 2 k78 2 ∧ glRowOK 2 (x2KeyTypes 2 k78 0) (x2KeyMult 2 k78 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k78 1) (x2KeyMult 2 k78 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k78 2) (x2KeyMult 2 k78 2) 512 = true ∧ gj369.length = x2KeySize 2 k78 ∧ x2KeySize 2 k78 ≤ 512 ∧ v369.length = 69 := by decide +kernel
theorem chk78 : trialKeyChk 2 k78 69 gj369 x2Trial_369 v369 :=
  trialKeyChk_intro 2 k78 69 gj369 x2Trial_369 v369 small78 gjok78 vok78

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k78, ibFS [(v369, v369, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN78 : N k78 = x2TrialForm 2 k78) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 4 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k78 69 _ gj369 x2Trial_369 v369 (by decide) (by rw [hN78]; exact trialForm_eq 2 k78 69 x2Trial_369 (by decide) rfl) chk78

end ThreeCopyQutritWerner.X2.InK2x246
