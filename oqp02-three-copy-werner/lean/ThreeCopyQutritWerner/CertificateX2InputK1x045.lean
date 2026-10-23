module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x045
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k24 : x2Key 1 := ⟨24, by decide⟩
x2_gj_cols gj146 146 1 0 4 5 256
theorem gjc24_0 : (List.range 9).all (fun d => gjCheck 256 1 0 4 5 1 7 7 (x2JCols 146 (0 + d)) (gj146.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok24 : ∀ d < x2KeySize 1 k24, gjCheck 256 1 (x2KeyTypes 1 k24 0) (x2KeyTypes 1 k24 1) (x2KeyTypes 1 k24 2) (x2KeyMult 1 k24 0) (x2KeyMult 1 k24 1) (x2KeyMult 1 k24 2) (x2JCols (x2KeyGlobal 1 k24) d) (gj146.getD d 0) = true := by
  have hr : x2KeySize 1 k24 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 4 5 1 7 7 (x2JCols 146 d) (gj146.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 4 5 1 7 7 (x2JCols 146 d) (gj146.getD d 0)) 0 9 gjc24_0 d (Nat.zero_le d) (by omega)
x2_v_cols v146 gj146 146 256 49
theorem vc24_0 : (List.range 3).all (fun c => vCheck 256 49 9 gj146 (x2Trial_146.getD (0 + c) 0) (v146.getD (0 + c) 0)) = true := by decide +kernel
theorem vok24 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k24 0 * x2KeyMult 1 k24 1 * x2KeyMult 1 k24 2) (x2KeySize 1 k24) gj146 (x2Trial_146.getD c 0) (v146.getD c 0) = true := by
  intro c hc
  show vCheck 256 49 9 gj146 (x2Trial_146.getD c 0) (v146.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 49 9 gj146 (x2Trial_146.getD c 0) (v146.getD c 0)) 0 3 vc24_0 c (Nat.zero_le c) (by omega)
theorem small24 : x2KeyDegree 1 k24 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k24 0 ∧ 1 ≤ x2KeyMult 1 k24 1 ∧ 1 ≤ x2KeyMult 1 k24 2 ∧ glRowOK 1 (x2KeyTypes 1 k24 0) (x2KeyMult 1 k24 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k24 1) (x2KeyMult 1 k24 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k24 2) (x2KeyMult 1 k24 2) 512 = true ∧ gj146.length = x2KeySize 1 k24 ∧ x2KeySize 1 k24 ≤ 512 ∧ v146.length = 3 := by decide +kernel
theorem chk24 : trialKeyChk 1 k24 3 gj146 x2Trial_146 v146 :=
  trialKeyChk_intro 1 k24 3 gj146 x2Trial_146 v146 small24 gjok24 vok24

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k24, ibFS [(v146, v146, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN24 : N k24 = x2TrialForm 1 k24) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 4 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k24 3 _ gj146 x2Trial_146 v146 (by decide) (by rw [hN24]; exact trialForm_eq 1 k24 3 x2Trial_146 (by decide) rfl) chk24

end ThreeCopyQutritWerner.X2.InK1x045
