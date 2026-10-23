module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x134
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k48 : x2Key 2 := ⟨48, by decide⟩
x2_gj_cols gj339 339 2 1 3 4 256
theorem gjc48_0 : (List.range 25).all (fun d => gjCheck 256 2 1 3 4 4 5 15 (x2JCols 339 (0 + d)) (gj339.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok48 : ∀ d < x2KeySize 2 k48, gjCheck 256 2 (x2KeyTypes 2 k48 0) (x2KeyTypes 2 k48 1) (x2KeyTypes 2 k48 2) (x2KeyMult 2 k48 0) (x2KeyMult 2 k48 1) (x2KeyMult 2 k48 2) (x2JCols (x2KeyGlobal 2 k48) d) (gj339.getD d 0) = true := by
  have hr : x2KeySize 2 k48 = 25 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 3 4 4 5 15 (x2JCols 339 d) (gj339.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 3 4 4 5 15 (x2JCols 339 d) (gj339.getD d 0)) 0 25 gjc48_0 d (Nat.zero_le d) (by omega)
x2_v_cols v339 gj339 339 256 300
theorem vc48_0 : (List.range 9).all (fun c => vCheck 256 300 25 gj339 (x2Trial_339.getD (0 + c) 0) (v339.getD (0 + c) 0)) = true := by decide +kernel
theorem vok48 : ∀ c < 9, vCheck 256 (x2KeyMult 2 k48 0 * x2KeyMult 2 k48 1 * x2KeyMult 2 k48 2) (x2KeySize 2 k48) gj339 (x2Trial_339.getD c 0) (v339.getD c 0) = true := by
  intro c hc
  show vCheck 256 300 25 gj339 (x2Trial_339.getD c 0) (v339.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 300 25 gj339 (x2Trial_339.getD c 0) (v339.getD c 0)) 0 9 vc48_0 c (Nat.zero_le c) (by omega)
theorem small48 : x2KeyDegree 2 k48 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k48 0 ∧ 1 ≤ x2KeyMult 2 k48 1 ∧ 1 ≤ x2KeyMult 2 k48 2 ∧ glRowOK 2 (x2KeyTypes 2 k48 0) (x2KeyMult 2 k48 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k48 1) (x2KeyMult 2 k48 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k48 2) (x2KeyMult 2 k48 2) 512 = true ∧ gj339.length = x2KeySize 2 k48 ∧ x2KeySize 2 k48 ≤ 512 ∧ v339.length = 9 := by decide +kernel
theorem chk48 : trialKeyChk 2 k48 9 gj339 x2Trial_339 v339 :=
  trialKeyChk_intro 2 k48 9 gj339 x2Trial_339 v339 small48 gjok48 vok48

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k48, ibFS [(v339, v339, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN48 : N k48 = x2TrialForm 2 k48) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 3 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k48 9 _ gj339 x2Trial_339 v339 (by decide) (by rw [hN48]; exact trialForm_eq 2 k48 9 x2Trial_339 (by decide) rfl) chk48

end ThreeCopyQutritWerner.X2.InK2x134
