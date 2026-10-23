module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 1, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x015
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k8 : x2Key 2 := ⟨8, by decide⟩
x2_gj_cols gj299 299 2 0 1 5 256
theorem gjc8_0 : (List.range 4).all (fun d => gjCheck 256 2 0 1 5 1 4 10 (x2JCols 299 (0 + d)) (gj299.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok8 : ∀ d < x2KeySize 2 k8, gjCheck 256 2 (x2KeyTypes 2 k8 0) (x2KeyTypes 2 k8 1) (x2KeyTypes 2 k8 2) (x2KeyMult 2 k8 0) (x2KeyMult 2 k8 1) (x2KeyMult 2 k8 2) (x2JCols (x2KeyGlobal 2 k8) d) (gj299.getD d 0) = true := by
  have hr : x2KeySize 2 k8 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 1 5 1 4 10 (x2JCols 299 d) (gj299.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 1 5 1 4 10 (x2JCols 299 d) (gj299.getD d 0)) 0 4 gjc8_0 d (Nat.zero_le d) (by omega)
x2_v_cols v299 gj299 299 256 40
theorem vc8_0 : (List.range 2).all (fun c => vCheck 256 40 4 gj299 (x2Trial_299.getD (0 + c) 0) (v299.getD (0 + c) 0)) = true := by decide +kernel
theorem vok8 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k8 0 * x2KeyMult 2 k8 1 * x2KeyMult 2 k8 2) (x2KeySize 2 k8) gj299 (x2Trial_299.getD c 0) (v299.getD c 0) = true := by
  intro c hc
  show vCheck 256 40 4 gj299 (x2Trial_299.getD c 0) (v299.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 40 4 gj299 (x2Trial_299.getD c 0) (v299.getD c 0)) 0 2 vc8_0 c (Nat.zero_le c) (by omega)
theorem small8 : x2KeyDegree 2 k8 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k8 0 ∧ 1 ≤ x2KeyMult 2 k8 1 ∧ 1 ≤ x2KeyMult 2 k8 2 ∧ glRowOK 2 (x2KeyTypes 2 k8 0) (x2KeyMult 2 k8 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k8 1) (x2KeyMult 2 k8 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k8 2) (x2KeyMult 2 k8 2) 512 = true ∧ gj299.length = x2KeySize 2 k8 ∧ x2KeySize 2 k8 ≤ 512 ∧ v299.length = 2 := by decide +kernel
theorem chk8 : trialKeyChk 2 k8 2 gj299 x2Trial_299 v299 :=
  trialKeyChk_intro 2 k8 2 gj299 x2Trial_299 v299 small8 gjok8 vok8

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k8, ibFS [(v299, v299, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN8 : N k8 = x2TrialForm 2 k8) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 1 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k8 2 _ gj299 x2Trial_299 v299 (by decide) (by rw [hN8]; exact trialForm_eq 2 k8 2 x2Trial_299 (by decide) rfl) chk8

end ThreeCopyQutritWerner.X2.InK2x015
