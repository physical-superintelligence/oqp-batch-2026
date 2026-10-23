module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x145
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k62 : x2Key 1 := ⟨62, by decide⟩
x2_gj_cols gj184 184 1 1 4 5 256
theorem gjc62_0 : (List.range 17).all (fun d => gjCheck 256 1 1 4 5 2 7 7 (x2JCols 184 (0 + d)) (gj184.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok62 : ∀ d < x2KeySize 1 k62, gjCheck 256 1 (x2KeyTypes 1 k62 0) (x2KeyTypes 1 k62 1) (x2KeyTypes 1 k62 2) (x2KeyMult 1 k62 0) (x2KeyMult 1 k62 1) (x2KeyMult 1 k62 2) (x2JCols (x2KeyGlobal 1 k62) d) (gj184.getD d 0) = true := by
  have hr : x2KeySize 1 k62 = 17 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 4 5 2 7 7 (x2JCols 184 d) (gj184.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 4 5 2 7 7 (x2JCols 184 d) (gj184.getD d 0)) 0 17 gjc62_0 d (Nat.zero_le d) (by omega)
x2_v_cols v184 gj184 184 256 98
theorem vc62_0 : (List.range 5).all (fun c => vCheck 256 98 17 gj184 (x2Trial_184.getD (0 + c) 0) (v184.getD (0 + c) 0)) = true := by decide +kernel
theorem vok62 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k62 0 * x2KeyMult 1 k62 1 * x2KeyMult 1 k62 2) (x2KeySize 1 k62) gj184 (x2Trial_184.getD c 0) (v184.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 17 gj184 (x2Trial_184.getD c 0) (v184.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 17 gj184 (x2Trial_184.getD c 0) (v184.getD c 0)) 0 5 vc62_0 c (Nat.zero_le c) (by omega)
theorem small62 : x2KeyDegree 1 k62 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k62 0 ∧ 1 ≤ x2KeyMult 1 k62 1 ∧ 1 ≤ x2KeyMult 1 k62 2 ∧ glRowOK 1 (x2KeyTypes 1 k62 0) (x2KeyMult 1 k62 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k62 1) (x2KeyMult 1 k62 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k62 2) (x2KeyMult 1 k62 2) 512 = true ∧ gj184.length = x2KeySize 1 k62 ∧ x2KeySize 1 k62 ≤ 512 ∧ v184.length = 5 := by decide +kernel
theorem chk62 : trialKeyChk 1 k62 5 gj184 x2Trial_184 v184 :=
  trialKeyChk_intro 1 k62 5 gj184 x2Trial_184 v184 small62 gjok62 vok62

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k62, ibFS [(v184, v184, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN62 : N k62 = x2TrialForm 1 k62) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 4 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k62 5 _ gj184 x2Trial_184 v184 (by decide) (by rw [hN62]; exact trialForm_eq 1 k62 5 x2Trial_184 (by decide) rfl) chk62

end ThreeCopyQutritWerner.X2.InK1x145
