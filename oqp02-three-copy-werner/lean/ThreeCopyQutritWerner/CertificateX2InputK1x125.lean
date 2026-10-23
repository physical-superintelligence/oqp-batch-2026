module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x125
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k51 : x2Key 1 := ⟨51, by decide⟩
x2_gj_cols gj173 173 1 1 2 5 256
theorem gjc51_0 : (List.range 4).all (fun d => gjCheck 256 1 1 2 5 2 2 7 (x2JCols 173 (0 + d)) (gj173.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok51 : ∀ d < x2KeySize 1 k51, gjCheck 256 1 (x2KeyTypes 1 k51 0) (x2KeyTypes 1 k51 1) (x2KeyTypes 1 k51 2) (x2KeyMult 1 k51 0) (x2KeyMult 1 k51 1) (x2KeyMult 1 k51 2) (x2JCols (x2KeyGlobal 1 k51) d) (gj173.getD d 0) = true := by
  have hr : x2KeySize 1 k51 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 2 5 2 2 7 (x2JCols 173 d) (gj173.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 2 5 2 2 7 (x2JCols 173 d) (gj173.getD d 0)) 0 4 gjc51_0 d (Nat.zero_le d) (by omega)
x2_v_cols v173 gj173 173 256 28
theorem vc51_0 : (List.range 1).all (fun c => vCheck 256 28 4 gj173 (x2Trial_173.getD (0 + c) 0) (v173.getD (0 + c) 0)) = true := by decide +kernel
theorem vok51 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k51 0 * x2KeyMult 1 k51 1 * x2KeyMult 1 k51 2) (x2KeySize 1 k51) gj173 (x2Trial_173.getD c 0) (v173.getD c 0) = true := by
  intro c hc
  show vCheck 256 28 4 gj173 (x2Trial_173.getD c 0) (v173.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 28 4 gj173 (x2Trial_173.getD c 0) (v173.getD c 0)) 0 1 vc51_0 c (Nat.zero_le c) (by omega)
theorem small51 : x2KeyDegree 1 k51 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k51 0 ∧ 1 ≤ x2KeyMult 1 k51 1 ∧ 1 ≤ x2KeyMult 1 k51 2 ∧ glRowOK 1 (x2KeyTypes 1 k51 0) (x2KeyMult 1 k51 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k51 1) (x2KeyMult 1 k51 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k51 2) (x2KeyMult 1 k51 2) 512 = true ∧ gj173.length = x2KeySize 1 k51 ∧ x2KeySize 1 k51 ≤ 512 ∧ v173.length = 1 := by decide +kernel
theorem chk51 : trialKeyChk 1 k51 1 gj173 x2Trial_173 v173 :=
  trialKeyChk_intro 1 k51 1 gj173 x2Trial_173 v173 small51 gjok51 vok51

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k51, ibFS [(v173, v173, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN51 : N k51 = x2TrialForm 1 k51) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 2 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k51 1 _ gj173 x2Trial_173 v173 (by decide) (by rw [hN51]; exact trialForm_eq 1 k51 1 x2Trial_173 (by decide) rfl) chk51

end ThreeCopyQutritWerner.X2.InK1x125
