module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x457
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k141 : x2Key 1 := ⟨141, by decide⟩
x2_gj_cols gj263 263 1 4 5 7 256
theorem gjc141_0 : (List.range 49).all (fun d => gjCheck 256 1 4 5 7 7 7 6 (x2JCols 263 (0 + d)) (gj263.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok141 : ∀ d < x2KeySize 1 k141, gjCheck 256 1 (x2KeyTypes 1 k141 0) (x2KeyTypes 1 k141 1) (x2KeyTypes 1 k141 2) (x2KeyMult 1 k141 0) (x2KeyMult 1 k141 1) (x2KeyMult 1 k141 2) (x2JCols (x2KeyGlobal 1 k141) d) (gj263.getD d 0) = true := by
  have hr : x2KeySize 1 k141 = 49 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 5 7 7 7 6 (x2JCols 263 d) (gj263.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 5 7 7 7 6 (x2JCols 263 d) (gj263.getD d 0)) 0 49 gjc141_0 d (Nat.zero_le d) (by omega)
x2_v_cols v263 gj263 263 256 294
theorem vc141_0 : (List.range 31).all (fun c => vCheck 256 294 49 gj263 (x2Trial_263.getD (0 + c) 0) (v263.getD (0 + c) 0)) = true := by decide +kernel
theorem vok141 : ∀ c < 31, vCheck 256 (x2KeyMult 1 k141 0 * x2KeyMult 1 k141 1 * x2KeyMult 1 k141 2) (x2KeySize 1 k141) gj263 (x2Trial_263.getD c 0) (v263.getD c 0) = true := by
  intro c hc
  show vCheck 256 294 49 gj263 (x2Trial_263.getD c 0) (v263.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 294 49 gj263 (x2Trial_263.getD c 0) (v263.getD c 0)) 0 31 vc141_0 c (Nat.zero_le c) (by omega)
theorem small141 : x2KeyDegree 1 k141 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k141 0 ∧ 1 ≤ x2KeyMult 1 k141 1 ∧ 1 ≤ x2KeyMult 1 k141 2 ∧ glRowOK 1 (x2KeyTypes 1 k141 0) (x2KeyMult 1 k141 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k141 1) (x2KeyMult 1 k141 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k141 2) (x2KeyMult 1 k141 2) 512 = true ∧ gj263.length = x2KeySize 1 k141 ∧ x2KeySize 1 k141 ≤ 512 ∧ v263.length = 31 := by decide +kernel
theorem chk141 : trialKeyChk 1 k141 31 gj263 x2Trial_263 v263 :=
  trialKeyChk_intro 1 k141 31 gj263 x2Trial_263 v263 small141 gjok141 vok141

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k141, ibFS [(v263, v263, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN141 : N k141 = x2TrialForm 1 k141) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k141 31 _ gj263 x2Trial_263 v263 (by decide) (by rw [hN141]; exact trialForm_eq 1 k141 31 x2Trial_263 (by decide) rfl) chk141

end ThreeCopyQutritWerner.X2.InK1x457
