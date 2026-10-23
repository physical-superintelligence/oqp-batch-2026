module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x134
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k56 : x2Key 1 := ⟨56, by decide⟩
x2_gj_cols gj178 178 1 1 3 4 256
theorem gjc56_0 : (List.range 21).all (fun d => gjCheck 256 1 1 3 4 2 9 7 (x2JCols 178 (0 + d)) (gj178.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok56 : ∀ d < x2KeySize 1 k56, gjCheck 256 1 (x2KeyTypes 1 k56 0) (x2KeyTypes 1 k56 1) (x2KeyTypes 1 k56 2) (x2KeyMult 1 k56 0) (x2KeyMult 1 k56 1) (x2KeyMult 1 k56 2) (x2JCols (x2KeyGlobal 1 k56) d) (gj178.getD d 0) = true := by
  have hr : x2KeySize 1 k56 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 3 4 2 9 7 (x2JCols 178 d) (gj178.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 3 4 2 9 7 (x2JCols 178 d) (gj178.getD d 0)) 0 21 gjc56_0 d (Nat.zero_le d) (by omega)
x2_v_cols v178 gj178 178 256 126
theorem vc56_0 : (List.range 2).all (fun c => vCheck 256 126 21 gj178 (x2Trial_178.getD (0 + c) 0) (v178.getD (0 + c) 0)) = true := by decide +kernel
theorem vok56 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k56 0 * x2KeyMult 1 k56 1 * x2KeyMult 1 k56 2) (x2KeySize 1 k56) gj178 (x2Trial_178.getD c 0) (v178.getD c 0) = true := by
  intro c hc
  show vCheck 256 126 21 gj178 (x2Trial_178.getD c 0) (v178.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 126 21 gj178 (x2Trial_178.getD c 0) (v178.getD c 0)) 0 2 vc56_0 c (Nat.zero_le c) (by omega)
theorem small56 : x2KeyDegree 1 k56 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k56 0 ∧ 1 ≤ x2KeyMult 1 k56 1 ∧ 1 ≤ x2KeyMult 1 k56 2 ∧ glRowOK 1 (x2KeyTypes 1 k56 0) (x2KeyMult 1 k56 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k56 1) (x2KeyMult 1 k56 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k56 2) (x2KeyMult 1 k56 2) 512 = true ∧ gj178.length = x2KeySize 1 k56 ∧ x2KeySize 1 k56 ≤ 512 ∧ v178.length = 2 := by decide +kernel
theorem chk56 : trialKeyChk 1 k56 2 gj178 x2Trial_178 v178 :=
  trialKeyChk_intro 1 k56 2 gj178 x2Trial_178 v178 small56 gjok56 vok56

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k56, ibFS [(v178, v178, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN56 : N k56 = x2TrialForm 1 k56) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 3 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k56 2 _ gj178 x2Trial_178 v178 (by decide) (by rw [hN56]; exact trialForm_eq 1 k56 2 x2Trial_178 (by decide) rfl) chk56

end ThreeCopyQutritWerner.X2.InK1x134
