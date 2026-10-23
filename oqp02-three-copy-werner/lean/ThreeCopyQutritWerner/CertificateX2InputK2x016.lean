module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 1, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x016
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k9 : x2Key 2 := ⟨9, by decide⟩
x2_gj_cols gj300 300 2 0 1 6 256
theorem gjc9_0 : (List.range 4).all (fun d => gjCheck 256 2 0 1 6 1 4 11 (x2JCols 300 (0 + d)) (gj300.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok9 : ∀ d < x2KeySize 2 k9, gjCheck 256 2 (x2KeyTypes 2 k9 0) (x2KeyTypes 2 k9 1) (x2KeyTypes 2 k9 2) (x2KeyMult 2 k9 0) (x2KeyMult 2 k9 1) (x2KeyMult 2 k9 2) (x2JCols (x2KeyGlobal 2 k9) d) (gj300.getD d 0) = true := by
  have hr : x2KeySize 2 k9 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 1 6 1 4 11 (x2JCols 300 d) (gj300.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 1 6 1 4 11 (x2JCols 300 d) (gj300.getD d 0)) 0 4 gjc9_0 d (Nat.zero_le d) (by omega)
x2_v_cols v300 gj300 300 256 44
theorem vc9_0 : (List.range 4).all (fun c => vCheck 256 44 4 gj300 (x2Trial_300.getD (0 + c) 0) (v300.getD (0 + c) 0)) = true := by decide +kernel
theorem vok9 : ∀ c < 4, vCheck 256 (x2KeyMult 2 k9 0 * x2KeyMult 2 k9 1 * x2KeyMult 2 k9 2) (x2KeySize 2 k9) gj300 (x2Trial_300.getD c 0) (v300.getD c 0) = true := by
  intro c hc
  show vCheck 256 44 4 gj300 (x2Trial_300.getD c 0) (v300.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 44 4 gj300 (x2Trial_300.getD c 0) (v300.getD c 0)) 0 4 vc9_0 c (Nat.zero_le c) (by omega)
theorem small9 : x2KeyDegree 2 k9 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k9 0 ∧ 1 ≤ x2KeyMult 2 k9 1 ∧ 1 ≤ x2KeyMult 2 k9 2 ∧ glRowOK 2 (x2KeyTypes 2 k9 0) (x2KeyMult 2 k9 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k9 1) (x2KeyMult 2 k9 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k9 2) (x2KeyMult 2 k9 2) 512 = true ∧ gj300.length = x2KeySize 2 k9 ∧ x2KeySize 2 k9 ≤ 512 ∧ v300.length = 4 := by decide +kernel
theorem chk9 : trialKeyChk 2 k9 4 gj300 x2Trial_300 v300 :=
  trialKeyChk_intro 2 k9 4 gj300 x2Trial_300 v300 small9 gjok9 vok9

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k9, ibFS [(v300, v300, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN9 : N k9 = x2TrialForm 2 k9) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 1 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k9 4 _ gj300 x2Trial_300 v300 (by decide) (by rw [hN9]; exact trialForm_eq 2 k9 4 x2Trial_300 (by decide) rfl) chk9

end ThreeCopyQutritWerner.X2.InK2x016
