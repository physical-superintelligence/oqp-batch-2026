module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x267
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k101 : x2Key 1 := ⟨101, by decide⟩
x2_gj_cols gj223 223 1 2 6 7 256
theorem gjc101_0 : (List.range 34).all (fun d => gjCheck 256 1 2 6 7 2 17 6 (x2JCols 223 (0 + d)) (gj223.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok101 : ∀ d < x2KeySize 1 k101, gjCheck 256 1 (x2KeyTypes 1 k101 0) (x2KeyTypes 1 k101 1) (x2KeyTypes 1 k101 2) (x2KeyMult 1 k101 0) (x2KeyMult 1 k101 1) (x2KeyMult 1 k101 2) (x2JCols (x2KeyGlobal 1 k101) d) (gj223.getD d 0) = true := by
  have hr : x2KeySize 1 k101 = 34 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 6 7 2 17 6 (x2JCols 223 d) (gj223.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 6 7 2 17 6 (x2JCols 223 d) (gj223.getD d 0)) 0 34 gjc101_0 d (Nat.zero_le d) (by omega)
x2_v_cols v223 gj223 223 256 204
theorem vc101_0 : (List.range 17).all (fun c => vCheck 256 204 34 gj223 (x2Trial_223.getD (0 + c) 0) (v223.getD (0 + c) 0)) = true := by decide +kernel
theorem vok101 : ∀ c < 17, vCheck 256 (x2KeyMult 1 k101 0 * x2KeyMult 1 k101 1 * x2KeyMult 1 k101 2) (x2KeySize 1 k101) gj223 (x2Trial_223.getD c 0) (v223.getD c 0) = true := by
  intro c hc
  show vCheck 256 204 34 gj223 (x2Trial_223.getD c 0) (v223.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 204 34 gj223 (x2Trial_223.getD c 0) (v223.getD c 0)) 0 17 vc101_0 c (Nat.zero_le c) (by omega)
theorem small101 : x2KeyDegree 1 k101 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k101 0 ∧ 1 ≤ x2KeyMult 1 k101 1 ∧ 1 ≤ x2KeyMult 1 k101 2 ∧ glRowOK 1 (x2KeyTypes 1 k101 0) (x2KeyMult 1 k101 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k101 1) (x2KeyMult 1 k101 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k101 2) (x2KeyMult 1 k101 2) 512 = true ∧ gj223.length = x2KeySize 1 k101 ∧ x2KeySize 1 k101 ≤ 512 ∧ v223.length = 17 := by decide +kernel
theorem chk101 : trialKeyChk 1 k101 17 gj223 x2Trial_223 v223 :=
  trialKeyChk_intro 1 k101 17 gj223 x2Trial_223 v223 small101 gjok101 vok101

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k101, ibFS [(v223, v223, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN101 : N k101 = x2TrialForm 1 k101) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k101 17 _ gj223 x2Trial_223 v223 (by decide) (by rw [hN101]; exact trialForm_eq 1 k101 17 x2Trial_223 (by decide) rfl) chk101

end ThreeCopyQutritWerner.X2.InK1x267
