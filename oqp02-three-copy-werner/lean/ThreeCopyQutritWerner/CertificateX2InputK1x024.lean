module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x024
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k12 : x2Key 1 := ⟨12, by decide⟩
x2_gj_cols gj134 134 1 0 2 4 256
theorem gjc12_0 : (List.range 3).all (fun d => gjCheck 256 1 0 2 4 1 2 7 (x2JCols 134 (0 + d)) (gj134.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok12 : ∀ d < x2KeySize 1 k12, gjCheck 256 1 (x2KeyTypes 1 k12 0) (x2KeyTypes 1 k12 1) (x2KeyTypes 1 k12 2) (x2KeyMult 1 k12 0) (x2KeyMult 1 k12 1) (x2KeyMult 1 k12 2) (x2JCols (x2KeyGlobal 1 k12) d) (gj134.getD d 0) = true := by
  have hr : x2KeySize 1 k12 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 2 4 1 2 7 (x2JCols 134 d) (gj134.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 2 4 1 2 7 (x2JCols 134 d) (gj134.getD d 0)) 0 3 gjc12_0 d (Nat.zero_le d) (by omega)
x2_v_cols v134 gj134 134 256 14
theorem vc12_0 : (List.range 1).all (fun c => vCheck 256 14 3 gj134 (x2Trial_134.getD (0 + c) 0) (v134.getD (0 + c) 0)) = true := by decide +kernel
theorem vok12 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k12 0 * x2KeyMult 1 k12 1 * x2KeyMult 1 k12 2) (x2KeySize 1 k12) gj134 (x2Trial_134.getD c 0) (v134.getD c 0) = true := by
  intro c hc
  show vCheck 256 14 3 gj134 (x2Trial_134.getD c 0) (v134.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 14 3 gj134 (x2Trial_134.getD c 0) (v134.getD c 0)) 0 1 vc12_0 c (Nat.zero_le c) (by omega)
theorem small12 : x2KeyDegree 1 k12 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k12 0 ∧ 1 ≤ x2KeyMult 1 k12 1 ∧ 1 ≤ x2KeyMult 1 k12 2 ∧ glRowOK 1 (x2KeyTypes 1 k12 0) (x2KeyMult 1 k12 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k12 1) (x2KeyMult 1 k12 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k12 2) (x2KeyMult 1 k12 2) 512 = true ∧ gj134.length = x2KeySize 1 k12 ∧ x2KeySize 1 k12 ≤ 512 ∧ v134.length = 1 := by decide +kernel
theorem chk12 : trialKeyChk 1 k12 1 gj134 x2Trial_134 v134 :=
  trialKeyChk_intro 1 k12 1 gj134 x2Trial_134 v134 small12 gjok12 vok12

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k12, ibFS [(v134, v134, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN12 : N k12 = x2TrialForm 1 k12) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 2 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k12 1 _ gj134 x2Trial_134 v134 (by decide) (by rw [hN12]; exact trialForm_eq 1 k12 1 x2Trial_134 (by decide) rfl) chk12

end ThreeCopyQutritWerner.X2.InK1x024
