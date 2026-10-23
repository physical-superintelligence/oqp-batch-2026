module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x256
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k97 : x2Key 1 := ⟨97, by decide⟩
x2_gj_cols gj219 219 1 2 5 6 256
theorem gjc97_0 : (List.range 39).all (fun d => gjCheck 256 1 2 5 6 2 7 17 (x2JCols 219 (0 + d)) (gj219.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok97 : ∀ d < x2KeySize 1 k97, gjCheck 256 1 (x2KeyTypes 1 k97 0) (x2KeyTypes 1 k97 1) (x2KeyTypes 1 k97 2) (x2KeyMult 1 k97 0) (x2KeyMult 1 k97 1) (x2KeyMult 1 k97 2) (x2JCols (x2KeyGlobal 1 k97) d) (gj219.getD d 0) = true := by
  have hr : x2KeySize 1 k97 = 39 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 5 6 2 7 17 (x2JCols 219 d) (gj219.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 5 6 2 7 17 (x2JCols 219 d) (gj219.getD d 0)) 0 39 gjc97_0 d (Nat.zero_le d) (by omega)
x2_v_cols v219 gj219 219 256 238
theorem vc97_0 : (List.range 18).all (fun c => vCheck 256 238 39 gj219 (x2Trial_219.getD (0 + c) 0) (v219.getD (0 + c) 0)) = true := by decide +kernel
theorem vok97 : ∀ c < 18, vCheck 256 (x2KeyMult 1 k97 0 * x2KeyMult 1 k97 1 * x2KeyMult 1 k97 2) (x2KeySize 1 k97) gj219 (x2Trial_219.getD c 0) (v219.getD c 0) = true := by
  intro c hc
  show vCheck 256 238 39 gj219 (x2Trial_219.getD c 0) (v219.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 238 39 gj219 (x2Trial_219.getD c 0) (v219.getD c 0)) 0 18 vc97_0 c (Nat.zero_le c) (by omega)
theorem small97 : x2KeyDegree 1 k97 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k97 0 ∧ 1 ≤ x2KeyMult 1 k97 1 ∧ 1 ≤ x2KeyMult 1 k97 2 ∧ glRowOK 1 (x2KeyTypes 1 k97 0) (x2KeyMult 1 k97 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k97 1) (x2KeyMult 1 k97 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k97 2) (x2KeyMult 1 k97 2) 512 = true ∧ gj219.length = x2KeySize 1 k97 ∧ x2KeySize 1 k97 ≤ 512 ∧ v219.length = 18 := by decide +kernel
theorem chk97 : trialKeyChk 1 k97 18 gj219 x2Trial_219 v219 :=
  trialKeyChk_intro 1 k97 18 gj219 x2Trial_219 v219 small97 gjok97 vok97

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k97, ibFS [(v219, v219, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN97 : N k97 = x2TrialForm 1 k97) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k97 18 _ gj219 x2Trial_219 v219 (by decide) (by rw [hN97]; exact trialForm_eq 1 k97 18 x2Trial_219 (by decide) rfl) chk97

end ThreeCopyQutritWerner.X2.InK1x256
