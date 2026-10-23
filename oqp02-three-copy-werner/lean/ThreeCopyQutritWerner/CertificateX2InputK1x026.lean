module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x026
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k14 : x2Key 1 := ⟨14, by decide⟩
x2_gj_cols gj136 136 1 0 2 6 256
theorem gjc14_0 : (List.range 5).all (fun d => gjCheck 256 1 0 2 6 1 2 17 (x2JCols 136 (0 + d)) (gj136.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok14 : ∀ d < x2KeySize 1 k14, gjCheck 256 1 (x2KeyTypes 1 k14 0) (x2KeyTypes 1 k14 1) (x2KeyTypes 1 k14 2) (x2KeyMult 1 k14 0) (x2KeyMult 1 k14 1) (x2KeyMult 1 k14 2) (x2JCols (x2KeyGlobal 1 k14) d) (gj136.getD d 0) = true := by
  have hr : x2KeySize 1 k14 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 2 6 1 2 17 (x2JCols 136 d) (gj136.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 2 6 1 2 17 (x2JCols 136 d) (gj136.getD d 0)) 0 5 gjc14_0 d (Nat.zero_le d) (by omega)
x2_v_cols v136 gj136 136 256 34
theorem vc14_0 : (List.range 2).all (fun c => vCheck 256 34 5 gj136 (x2Trial_136.getD (0 + c) 0) (v136.getD (0 + c) 0)) = true := by decide +kernel
theorem vok14 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k14 0 * x2KeyMult 1 k14 1 * x2KeyMult 1 k14 2) (x2KeySize 1 k14) gj136 (x2Trial_136.getD c 0) (v136.getD c 0) = true := by
  intro c hc
  show vCheck 256 34 5 gj136 (x2Trial_136.getD c 0) (v136.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 34 5 gj136 (x2Trial_136.getD c 0) (v136.getD c 0)) 0 2 vc14_0 c (Nat.zero_le c) (by omega)
theorem small14 : x2KeyDegree 1 k14 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k14 0 ∧ 1 ≤ x2KeyMult 1 k14 1 ∧ 1 ≤ x2KeyMult 1 k14 2 ∧ glRowOK 1 (x2KeyTypes 1 k14 0) (x2KeyMult 1 k14 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k14 1) (x2KeyMult 1 k14 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k14 2) (x2KeyMult 1 k14 2) 512 = true ∧ gj136.length = x2KeySize 1 k14 ∧ x2KeySize 1 k14 ≤ 512 ∧ v136.length = 2 := by decide +kernel
theorem chk14 : trialKeyChk 1 k14 2 gj136 x2Trial_136 v136 :=
  trialKeyChk_intro 1 k14 2 gj136 x2Trial_136 v136 small14 gjok14 vok14

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k14, ibFS [(v136, v136, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN14 : N k14 = x2TrialForm 1 k14) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 2 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k14 2 _ gj136 x2Trial_136 v136 (by decide) (by rw [hN14]; exact trialForm_eq 1 k14 2 x2Trial_136 (by decide) rfl) chk14

end ThreeCopyQutritWerner.X2.InK1x026
