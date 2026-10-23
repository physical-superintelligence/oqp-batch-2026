module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x145
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k53 : x2Key 2 := ⟨53, by decide⟩
x2_gj_cols gj344 344 2 1 4 5 256
theorem gjc53_0 : (List.range 50).all (fun d => gjCheck 256 2 1 4 5 4 15 10 (x2JCols 344 (0 + d)) (gj344.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok53 : ∀ d < x2KeySize 2 k53, gjCheck 256 2 (x2KeyTypes 2 k53 0) (x2KeyTypes 2 k53 1) (x2KeyTypes 2 k53 2) (x2KeyMult 2 k53 0) (x2KeyMult 2 k53 1) (x2KeyMult 2 k53 2) (x2JCols (x2KeyGlobal 2 k53) d) (gj344.getD d 0) = true := by
  have hr : x2KeySize 2 k53 = 50 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 4 5 4 15 10 (x2JCols 344 d) (gj344.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 4 5 4 15 10 (x2JCols 344 d) (gj344.getD d 0)) 0 50 gjc53_0 d (Nat.zero_le d) (by omega)
x2_v_cols v344 gj344 344 256 600
theorem vc53_0 : (List.range 34).all (fun c => vCheck 256 600 50 gj344 (x2Trial_344.getD (0 + c) 0) (v344.getD (0 + c) 0)) = true := by decide +kernel
theorem vok53 : ∀ c < 34, vCheck 256 (x2KeyMult 2 k53 0 * x2KeyMult 2 k53 1 * x2KeyMult 2 k53 2) (x2KeySize 2 k53) gj344 (x2Trial_344.getD c 0) (v344.getD c 0) = true := by
  intro c hc
  show vCheck 256 600 50 gj344 (x2Trial_344.getD c 0) (v344.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 600 50 gj344 (x2Trial_344.getD c 0) (v344.getD c 0)) 0 34 vc53_0 c (Nat.zero_le c) (by omega)
theorem small53 : x2KeyDegree 2 k53 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k53 0 ∧ 1 ≤ x2KeyMult 2 k53 1 ∧ 1 ≤ x2KeyMult 2 k53 2 ∧ glRowOK 2 (x2KeyTypes 2 k53 0) (x2KeyMult 2 k53 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k53 1) (x2KeyMult 2 k53 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k53 2) (x2KeyMult 2 k53 2) 512 = true ∧ gj344.length = x2KeySize 2 k53 ∧ x2KeySize 2 k53 ≤ 512 ∧ v344.length = 34 := by decide +kernel
theorem chk53 : trialKeyChk 2 k53 34 gj344 x2Trial_344 v344 :=
  trialKeyChk_intro 2 k53 34 gj344 x2Trial_344 v344 small53 gjok53 vok53

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k53, ibFS [(v344, v344, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN53 : N k53 = x2TrialForm 2 k53) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 4 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k53 34 _ gj344 x2Trial_344 v344 (by decide) (by rw [hN53]; exact trialForm_eq 2 k53 34 x2Trial_344 (by decide) rfl) chk53

end ThreeCopyQutritWerner.X2.InK2x145
