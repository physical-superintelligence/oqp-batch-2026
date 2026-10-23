module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x224
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k76 : x2Key 1 := ⟨76, by decide⟩
x2_gj_cols gj198 198 1 2 2 4 256
theorem gjc76_0 : (List.range 4).all (fun d => gjCheck 256 1 2 2 4 2 2 7 (x2JCols 198 (0 + d)) (gj198.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok76 : ∀ d < x2KeySize 1 k76, gjCheck 256 1 (x2KeyTypes 1 k76 0) (x2KeyTypes 1 k76 1) (x2KeyTypes 1 k76 2) (x2KeyMult 1 k76 0) (x2KeyMult 1 k76 1) (x2KeyMult 1 k76 2) (x2JCols (x2KeyGlobal 1 k76) d) (gj198.getD d 0) = true := by
  have hr : x2KeySize 1 k76 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 2 4 2 2 7 (x2JCols 198 d) (gj198.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 2 4 2 2 7 (x2JCols 198 d) (gj198.getD d 0)) 0 4 gjc76_0 d (Nat.zero_le d) (by omega)
x2_v_cols v198 gj198 198 256 28
theorem vc76_0 : (List.range 1).all (fun c => vCheck 256 28 4 gj198 (x2Trial_198.getD (0 + c) 0) (v198.getD (0 + c) 0)) = true := by decide +kernel
theorem vok76 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k76 0 * x2KeyMult 1 k76 1 * x2KeyMult 1 k76 2) (x2KeySize 1 k76) gj198 (x2Trial_198.getD c 0) (v198.getD c 0) = true := by
  intro c hc
  show vCheck 256 28 4 gj198 (x2Trial_198.getD c 0) (v198.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 28 4 gj198 (x2Trial_198.getD c 0) (v198.getD c 0)) 0 1 vc76_0 c (Nat.zero_le c) (by omega)
theorem small76 : x2KeyDegree 1 k76 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k76 0 ∧ 1 ≤ x2KeyMult 1 k76 1 ∧ 1 ≤ x2KeyMult 1 k76 2 ∧ glRowOK 1 (x2KeyTypes 1 k76 0) (x2KeyMult 1 k76 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k76 1) (x2KeyMult 1 k76 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k76 2) (x2KeyMult 1 k76 2) 512 = true ∧ gj198.length = x2KeySize 1 k76 ∧ x2KeySize 1 k76 ≤ 512 ∧ v198.length = 1 := by decide +kernel
theorem chk76 : trialKeyChk 1 k76 1 gj198 x2Trial_198 v198 :=
  trialKeyChk_intro 1 k76 1 gj198 x2Trial_198 v198 small76 gjok76 vok76
def k77 : x2Key 1 := ⟨77, by decide⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k76, ibFS [(v198, v198, 94810963968000)]), (k77, [])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN76 : N k76 = x2TrialForm 1 k76) (hN77 : N k77 = x2TrialForm 1 k77) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 2 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k76 1 _ gj198 x2Trial_198 v198 (by decide) (by rw [hN76]; exact trialForm_eq 1 k76 1 x2Trial_198 (by decide) rfl) chk76
  · exact keyOK_of_zeroBlock _ 1 N k77 (by rw [hN77]; exact trialForm_zero 1 k77 (by decide))

end ThreeCopyQutritWerner.X2.InK1x224
