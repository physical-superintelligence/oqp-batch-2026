module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x127
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k53 : x2Key 1 := ⟨53, by decide⟩
x2_gj_cols gj175 175 1 1 2 7 256
theorem gjc53_0 : (List.range 4).all (fun d => gjCheck 256 1 1 2 7 2 2 6 (x2JCols 175 (0 + d)) (gj175.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok53 : ∀ d < x2KeySize 1 k53, gjCheck 256 1 (x2KeyTypes 1 k53 0) (x2KeyTypes 1 k53 1) (x2KeyTypes 1 k53 2) (x2KeyMult 1 k53 0) (x2KeyMult 1 k53 1) (x2KeyMult 1 k53 2) (x2JCols (x2KeyGlobal 1 k53) d) (gj175.getD d 0) = true := by
  have hr : x2KeySize 1 k53 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 2 7 2 2 6 (x2JCols 175 d) (gj175.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 2 7 2 2 6 (x2JCols 175 d) (gj175.getD d 0)) 0 4 gjc53_0 d (Nat.zero_le d) (by omega)
x2_v_cols v175 gj175 175 256 24
theorem vc53_0 : (List.range 1).all (fun c => vCheck 256 24 4 gj175 (x2Trial_175.getD (0 + c) 0) (v175.getD (0 + c) 0)) = true := by decide +kernel
theorem vok53 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k53 0 * x2KeyMult 1 k53 1 * x2KeyMult 1 k53 2) (x2KeySize 1 k53) gj175 (x2Trial_175.getD c 0) (v175.getD c 0) = true := by
  intro c hc
  show vCheck 256 24 4 gj175 (x2Trial_175.getD c 0) (v175.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 24 4 gj175 (x2Trial_175.getD c 0) (v175.getD c 0)) 0 1 vc53_0 c (Nat.zero_le c) (by omega)
theorem small53 : x2KeyDegree 1 k53 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k53 0 ∧ 1 ≤ x2KeyMult 1 k53 1 ∧ 1 ≤ x2KeyMult 1 k53 2 ∧ glRowOK 1 (x2KeyTypes 1 k53 0) (x2KeyMult 1 k53 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k53 1) (x2KeyMult 1 k53 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k53 2) (x2KeyMult 1 k53 2) 512 = true ∧ gj175.length = x2KeySize 1 k53 ∧ x2KeySize 1 k53 ≤ 512 ∧ v175.length = 1 := by decide +kernel
theorem chk53 : trialKeyChk 1 k53 1 gj175 x2Trial_175 v175 :=
  trialKeyChk_intro 1 k53 1 gj175 x2Trial_175 v175 small53 gjok53 vok53

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k53, ibFS [(v175, v175, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN53 : N k53 = x2TrialForm 1 k53) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 2 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k53 1 _ gj175 x2Trial_175 v175 (by decide) (by rw [hN53]; exact trialForm_eq 1 k53 1 x2Trial_175 (by decide) rfl) chk53

end ThreeCopyQutritWerner.X2.InK1x127
