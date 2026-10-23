module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x034
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k16 : x2Key 2 := ⟨16, by decide⟩
x2_gj_cols gj307 307 2 0 3 4 256
theorem gjc16_0 : (List.range 6).all (fun d => gjCheck 256 2 0 3 4 1 5 15 (x2JCols 307 (0 + d)) (gj307.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok16 : ∀ d < x2KeySize 2 k16, gjCheck 256 2 (x2KeyTypes 2 k16 0) (x2KeyTypes 2 k16 1) (x2KeyTypes 2 k16 2) (x2KeyMult 2 k16 0) (x2KeyMult 2 k16 1) (x2KeyMult 2 k16 2) (x2JCols (x2KeyGlobal 2 k16) d) (gj307.getD d 0) = true := by
  have hr : x2KeySize 2 k16 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 3 4 1 5 15 (x2JCols 307 d) (gj307.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 3 4 1 5 15 (x2JCols 307 d) (gj307.getD d 0)) 0 6 gjc16_0 d (Nat.zero_le d) (by omega)
x2_v_cols v307 gj307 307 256 75
theorem vc16_0 : (List.range 2).all (fun c => vCheck 256 75 6 gj307 (x2Trial_307.getD (0 + c) 0) (v307.getD (0 + c) 0)) = true := by decide +kernel
theorem vok16 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k16 0 * x2KeyMult 2 k16 1 * x2KeyMult 2 k16 2) (x2KeySize 2 k16) gj307 (x2Trial_307.getD c 0) (v307.getD c 0) = true := by
  intro c hc
  show vCheck 256 75 6 gj307 (x2Trial_307.getD c 0) (v307.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 75 6 gj307 (x2Trial_307.getD c 0) (v307.getD c 0)) 0 2 vc16_0 c (Nat.zero_le c) (by omega)
theorem small16 : x2KeyDegree 2 k16 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k16 0 ∧ 1 ≤ x2KeyMult 2 k16 1 ∧ 1 ≤ x2KeyMult 2 k16 2 ∧ glRowOK 2 (x2KeyTypes 2 k16 0) (x2KeyMult 2 k16 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k16 1) (x2KeyMult 2 k16 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k16 2) (x2KeyMult 2 k16 2) 512 = true ∧ gj307.length = x2KeySize 2 k16 ∧ x2KeySize 2 k16 ≤ 512 ∧ v307.length = 2 := by decide +kernel
theorem chk16 : trialKeyChk 2 k16 2 gj307 x2Trial_307 v307 :=
  trialKeyChk_intro 2 k16 2 gj307 x2Trial_307 v307 small16 gjok16 vok16

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k16, ibFS [(v307, v307, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN16 : N k16 = x2TrialForm 2 k16) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 3 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k16 2 _ gj307 x2Trial_307 v307 (by decide) (by rw [hN16]; exact trialForm_eq 2 k16 2 x2Trial_307 (by decide) rfl) chk16

end ThreeCopyQutritWerner.X2.InK2x034
