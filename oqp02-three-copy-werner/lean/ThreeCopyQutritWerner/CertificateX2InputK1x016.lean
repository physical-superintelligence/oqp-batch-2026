module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 1, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x016
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k9 : x2Key 1 := ⟨9, by decide⟩
x2_gj_cols gj131 131 1 0 1 6 256
theorem gjc9_0 : (List.range 6).all (fun d => gjCheck 256 1 0 1 6 1 2 17 (x2JCols 131 (0 + d)) (gj131.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok9 : ∀ d < x2KeySize 1 k9, gjCheck 256 1 (x2KeyTypes 1 k9 0) (x2KeyTypes 1 k9 1) (x2KeyTypes 1 k9 2) (x2KeyMult 1 k9 0) (x2KeyMult 1 k9 1) (x2KeyMult 1 k9 2) (x2JCols (x2KeyGlobal 1 k9) d) (gj131.getD d 0) = true := by
  have hr : x2KeySize 1 k9 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 1 6 1 2 17 (x2JCols 131 d) (gj131.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 1 6 1 2 17 (x2JCols 131 d) (gj131.getD d 0)) 0 6 gjc9_0 d (Nat.zero_le d) (by omega)
x2_v_cols v131 gj131 131 256 34
theorem vc9_0 : (List.range 1).all (fun c => vCheck 256 34 6 gj131 (x2Trial_131.getD (0 + c) 0) (v131.getD (0 + c) 0)) = true := by decide +kernel
theorem vok9 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k9 0 * x2KeyMult 1 k9 1 * x2KeyMult 1 k9 2) (x2KeySize 1 k9) gj131 (x2Trial_131.getD c 0) (v131.getD c 0) = true := by
  intro c hc
  show vCheck 256 34 6 gj131 (x2Trial_131.getD c 0) (v131.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 34 6 gj131 (x2Trial_131.getD c 0) (v131.getD c 0)) 0 1 vc9_0 c (Nat.zero_le c) (by omega)
theorem small9 : x2KeyDegree 1 k9 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k9 0 ∧ 1 ≤ x2KeyMult 1 k9 1 ∧ 1 ≤ x2KeyMult 1 k9 2 ∧ glRowOK 1 (x2KeyTypes 1 k9 0) (x2KeyMult 1 k9 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k9 1) (x2KeyMult 1 k9 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k9 2) (x2KeyMult 1 k9 2) 512 = true ∧ gj131.length = x2KeySize 1 k9 ∧ x2KeySize 1 k9 ≤ 512 ∧ v131.length = 1 := by decide +kernel
theorem chk9 : trialKeyChk 1 k9 1 gj131 x2Trial_131 v131 :=
  trialKeyChk_intro 1 k9 1 gj131 x2Trial_131 v131 small9 gjok9 vok9

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k9, ibFS [(v131, v131, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN9 : N k9 = x2TrialForm 1 k9) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 1 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k9 1 _ gj131 x2Trial_131 v131 (by decide) (by rw [hN9]; exact trialForm_eq 1 k9 1 x2Trial_131 (by decide) rfl) chk9

end ThreeCopyQutritWerner.X2.InK1x016
