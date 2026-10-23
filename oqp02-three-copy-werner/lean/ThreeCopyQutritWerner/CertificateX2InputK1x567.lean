module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x567
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k156 : x2Key 1 := ⟨156, by decide⟩
x2_gj_cols gj278 278 1 5 6 7 256
theorem gjc156_0 : (List.range 119).all (fun d => gjCheck 256 1 5 6 7 7 17 6 (x2JCols 278 (0 + d)) (gj278.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok156 : ∀ d < x2KeySize 1 k156, gjCheck 256 1 (x2KeyTypes 1 k156 0) (x2KeyTypes 1 k156 1) (x2KeyTypes 1 k156 2) (x2KeyMult 1 k156 0) (x2KeyMult 1 k156 1) (x2KeyMult 1 k156 2) (x2JCols (x2KeyGlobal 1 k156) d) (gj278.getD d 0) = true := by
  have hr : x2KeySize 1 k156 = 119 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 6 7 7 17 6 (x2JCols 278 d) (gj278.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 6 7 7 17 6 (x2JCols 278 d) (gj278.getD d 0)) 0 119 gjc156_0 d (Nat.zero_le d) (by omega)
x2_v_cols v278 gj278 278 256 714
theorem vc156_0 : (List.range 82).all (fun c => vCheck 256 714 119 gj278 (x2Trial_278.getD (0 + c) 0) (v278.getD (0 + c) 0)) = true := by decide +kernel
theorem vok156 : ∀ c < 82, vCheck 256 (x2KeyMult 1 k156 0 * x2KeyMult 1 k156 1 * x2KeyMult 1 k156 2) (x2KeySize 1 k156) gj278 (x2Trial_278.getD c 0) (v278.getD c 0) = true := by
  intro c hc
  show vCheck 256 714 119 gj278 (x2Trial_278.getD c 0) (v278.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 714 119 gj278 (x2Trial_278.getD c 0) (v278.getD c 0)) 0 82 vc156_0 c (Nat.zero_le c) (by omega)
theorem small156 : x2KeyDegree 1 k156 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k156 0 ∧ 1 ≤ x2KeyMult 1 k156 1 ∧ 1 ≤ x2KeyMult 1 k156 2 ∧ glRowOK 1 (x2KeyTypes 1 k156 0) (x2KeyMult 1 k156 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k156 1) (x2KeyMult 1 k156 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k156 2) (x2KeyMult 1 k156 2) 512 = true ∧ gj278.length = x2KeySize 1 k156 ∧ x2KeySize 1 k156 ≤ 512 ∧ v278.length = 82 := by decide +kernel
theorem chk156 : trialKeyChk 1 k156 82 gj278 x2Trial_278 v278 :=
  trialKeyChk_intro 1 k156 82 gj278 x2Trial_278 v278 small156 gjok156 vok156

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k156, ibFS [(v278, v278, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN156 : N k156 = x2TrialForm 1 k156) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k156 82 _ gj278 x2Trial_278 v278 (by decide) (by rw [hN156]; exact trialForm_eq 1 k156 82 x2Trial_278 (by decide) rfl) chk156

end ThreeCopyQutritWerner.X2.InK1x567
