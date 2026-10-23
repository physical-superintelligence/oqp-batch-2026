module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x157
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k68 : x2Key 1 := ⟨68, by decide⟩
x2_gj_cols gj190 190 1 1 5 7 256
theorem gjc68_0 : (List.range 14).all (fun d => gjCheck 256 1 1 5 7 2 7 6 (x2JCols 190 (0 + d)) (gj190.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok68 : ∀ d < x2KeySize 1 k68, gjCheck 256 1 (x2KeyTypes 1 k68 0) (x2KeyTypes 1 k68 1) (x2KeyTypes 1 k68 2) (x2KeyMult 1 k68 0) (x2KeyMult 1 k68 1) (x2KeyMult 1 k68 2) (x2JCols (x2KeyGlobal 1 k68) d) (gj190.getD d 0) = true := by
  have hr : x2KeySize 1 k68 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 5 7 2 7 6 (x2JCols 190 d) (gj190.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 5 7 2 7 6 (x2JCols 190 d) (gj190.getD d 0)) 0 14 gjc68_0 d (Nat.zero_le d) (by omega)
x2_v_cols v190 gj190 190 256 84
theorem vc68_0 : (List.range 5).all (fun c => vCheck 256 84 14 gj190 (x2Trial_190.getD (0 + c) 0) (v190.getD (0 + c) 0)) = true := by decide +kernel
theorem vok68 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k68 0 * x2KeyMult 1 k68 1 * x2KeyMult 1 k68 2) (x2KeySize 1 k68) gj190 (x2Trial_190.getD c 0) (v190.getD c 0) = true := by
  intro c hc
  show vCheck 256 84 14 gj190 (x2Trial_190.getD c 0) (v190.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 84 14 gj190 (x2Trial_190.getD c 0) (v190.getD c 0)) 0 5 vc68_0 c (Nat.zero_le c) (by omega)
theorem small68 : x2KeyDegree 1 k68 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k68 0 ∧ 1 ≤ x2KeyMult 1 k68 1 ∧ 1 ≤ x2KeyMult 1 k68 2 ∧ glRowOK 1 (x2KeyTypes 1 k68 0) (x2KeyMult 1 k68 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k68 1) (x2KeyMult 1 k68 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k68 2) (x2KeyMult 1 k68 2) 512 = true ∧ gj190.length = x2KeySize 1 k68 ∧ x2KeySize 1 k68 ≤ 512 ∧ v190.length = 5 := by decide +kernel
theorem chk68 : trialKeyChk 1 k68 5 gj190 x2Trial_190 v190 :=
  trialKeyChk_intro 1 k68 5 gj190 x2Trial_190 v190 small68 gjok68 vok68

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k68, ibFS [(v190, v190, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN68 : N k68 = x2TrialForm 1 k68) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k68 5 _ gj190 x2Trial_190 v190 (by decide) (by rw [hN68]; exact trialForm_eq 1 k68 5 x2Trial_190 (by decide) rfl) chk68

end ThreeCopyQutritWerner.X2.InK1x157
