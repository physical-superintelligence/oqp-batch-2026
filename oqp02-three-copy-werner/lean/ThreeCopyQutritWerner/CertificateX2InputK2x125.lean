module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x125
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k44 : x2Key 2 := ⟨44, by decide⟩
x2_gj_cols gj335 335 2 1 2 5 256
theorem gjc44_0 : (List.range 18).all (fun d => gjCheck 256 2 1 2 5 4 5 10 (x2JCols 335 (0 + d)) (gj335.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok44 : ∀ d < x2KeySize 2 k44, gjCheck 256 2 (x2KeyTypes 2 k44 0) (x2KeyTypes 2 k44 1) (x2KeyTypes 2 k44 2) (x2KeyMult 2 k44 0) (x2KeyMult 2 k44 1) (x2KeyMult 2 k44 2) (x2JCols (x2KeyGlobal 2 k44) d) (gj335.getD d 0) = true := by
  have hr : x2KeySize 2 k44 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 2 5 4 5 10 (x2JCols 335 d) (gj335.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 2 5 4 5 10 (x2JCols 335 d) (gj335.getD d 0)) 0 18 gjc44_0 d (Nat.zero_le d) (by omega)
x2_v_cols v335 gj335 335 256 200
theorem vc44_0 : (List.range 9).all (fun c => vCheck 256 200 18 gj335 (x2Trial_335.getD (0 + c) 0) (v335.getD (0 + c) 0)) = true := by decide +kernel
theorem vok44 : ∀ c < 9, vCheck 256 (x2KeyMult 2 k44 0 * x2KeyMult 2 k44 1 * x2KeyMult 2 k44 2) (x2KeySize 2 k44) gj335 (x2Trial_335.getD c 0) (v335.getD c 0) = true := by
  intro c hc
  show vCheck 256 200 18 gj335 (x2Trial_335.getD c 0) (v335.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 200 18 gj335 (x2Trial_335.getD c 0) (v335.getD c 0)) 0 9 vc44_0 c (Nat.zero_le c) (by omega)
theorem small44 : x2KeyDegree 2 k44 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k44 0 ∧ 1 ≤ x2KeyMult 2 k44 1 ∧ 1 ≤ x2KeyMult 2 k44 2 ∧ glRowOK 2 (x2KeyTypes 2 k44 0) (x2KeyMult 2 k44 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k44 1) (x2KeyMult 2 k44 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k44 2) (x2KeyMult 2 k44 2) 512 = true ∧ gj335.length = x2KeySize 2 k44 ∧ x2KeySize 2 k44 ≤ 512 ∧ v335.length = 9 := by decide +kernel
theorem chk44 : trialKeyChk 2 k44 9 gj335 x2Trial_335 v335 :=
  trialKeyChk_intro 2 k44 9 gj335 x2Trial_335 v335 small44 gjok44 vok44

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k44, ibFS [(v335, v335, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 2, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN44 : N k44 = x2TrialForm 2 k44) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 2 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k44 9 _ gj335 x2Trial_335 v335 (by decide) (by rw [hN44]; exact trialForm_eq 2 k44 9 x2Trial_335 (by decide) rfl) chk44

end ThreeCopyQutritWerner.X2.InK2x125
