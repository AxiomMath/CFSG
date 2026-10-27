module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8CandChk
public import Certificates.Kernel.TwoHSLe4.RawB
public import Certificates.Kernel.TwoHSLe4.CandData
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
public import CFSG.Certificates.Kernel.Common.Harness
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelTwoHSLe4

open CFSG.EvenSporadicStandard.TwoHS

@[expose] def candOk (a : R4) (w : R4 × R4 × ℕ) : Bool :=
  bif w.2.2 == 0 then
    r4eq (rmul w.2.1 a) R4.one && memR w.1 q0R && rveq (rmv w.1 zpRV) zpRV &&
      !memR (rmul (rmul w.2.1 w.1) a) q0R
  else bif w.2.2 == 1 then !memR (rmul a a) q0R
  else memR w.1 repsR && memR w.2.1 q0R &&
    bif w.2.2 == 2 then r4eq a (rmul (rmul w.1 (toR4 alpha1)) w.2.1)
    else w.2.2 == 3 && r4eq a (rmul (rmul w.1 (toR4 alpha2)) w.2.1)

@[expose] def candAll (l : List R4) : List (R4 × R4 × ℕ) → Bool :=
  List.rec (motive := fun _ => List (R4 × R4 × ℕ) → Bool) (fun _ => true)
    (fun a _ ih ws => List.rec (motive := fun _ => Bool) false
      (fun w ws' _ => candOk a w && ih ws') ws) l

theorem candAll_sound {l : List R4} {ws : List (R4 × R4 × ℕ)} (h : candAll l ws = true) :
    ∀ a ∈ l, ∃ w, candOk a w = true := by
  induction l generalizing ws with
  | nil => simp
  | cons a l ih =>
    cases ws with
    | nil =>
      change false = true at h
      exact absurd h Bool.false_ne_true
    | cons w ws =>
      change (candOk a w && candAll l ws) = true at h
      rw [Bool.and_eq_true] at h
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨w, h.1⟩
      · exact ih h.2 b hb

theorem rmul_assoc (a b c : R4) : rmul (rmul a b) c = rmul a (rmul b c) :=
  ofR4_inj (wf_rmul _ _) (wf_rmul _ _)
    (by rw [ofR4_rmul, ofR4_rmul, ofR4_rmul, ofR4_rmul, mul_assoc])

theorem rmul_one_left {q : R4} (hq : q.wf) : rmul R4.one q = q :=
  ofR4_inj (wf_rmul _ _) hq (by rw [ofR4_rmul, ofR4_one, one_mul])

theorem wf_of_mem_q0R {q : R4} (hq : q ∈ q0R) : q.wf := by
  obtain ⟨Q, _, rfl⟩ := List.mem_map.1 hq
  exact wf_toR4 Q

theorem craw_of
    (h1 : allR (fun a => rveq (rmv a tRV) zpRV && rveq (rmv a zpRV) tRV) candR = true)
    (h2 : allR (fun α => memR α candR) alphaRepsR = true) (h3 : candAll candR candW = true) :
    CRaw := by
  refine ⟨fun a ha => ?_, fun α hα => memR_iff.1 (allR_iff.1 h2 α hα), fun a ha hH hsq => ?_⟩
  · have h := allR_iff.1 h1 a ha
    rw [Bool.and_eq_true, rveq_iff, rveq_iff] at h
    exact h
  obtain ⟨⟨x, y, k⟩, hw⟩ := candAll_sound h3 a ha
  unfold candOk at hw
  dsimp only at hw
  by_cases h0 : (k == 0) = true
  · rw [h0, cond_true] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', r4eq_iff, rveq_iff, memR_iff] at hw
    obtain ⟨⟨⟨hya, hx⟩, hxz⟩, hn⟩ := hw
    obtain ⟨q, hq, hpq⟩ := hH x hx hxz
    have hz : rmul (rmul y x) a = q := by
      rw [rmul_assoc, hpq, ← rmul_assoc, hya, rmul_one_left (wf_of_mem_q0R hq)]
    have hm := memR_iff.2 (hz ▸ hq)
    rw [hn] at hm
    exact absurd hm Bool.false_ne_true
  rw [Bool.not_eq_true] at h0
  rw [h0, cond_false] at hw
  by_cases h1' : (k == 1) = true
  · rw [h1', cond_true, Bool.not_eq_true'] at hw
    have hm := memR_iff.2 hsq
    rw [hw] at hm
    exact absurd hm Bool.false_ne_true
  rw [Bool.not_eq_true] at h1'
  rw [h1', cond_false, Bool.and_eq_true, Bool.and_eq_true, memR_iff, memR_iff] at hw
  obtain ⟨⟨hx, hy⟩, hk⟩ := hw
  by_cases h2' : (k == 2) = true
  · rw [h2', cond_true, r4eq_iff] at hk
    exact ⟨toR4 alpha1, List.mem_map_of_mem (by simp [alphaReps]), x, hx, y, hy, hk⟩
  rw [Bool.not_eq_true] at h2'
  rw [h2', cond_false, Bool.and_eq_true, r4eq_iff] at hk
  exact ⟨toR4 alpha2, List.mem_map_of_mem (by simp [alphaReps]), x, hx, y, hy, hk.2⟩

set_option maxHeartbeats 0 in
theorem candR_swap :
    allR (fun a => rveq (rmv a tRV) zpRV && rveq (rmv a zpRV) tRV) candR = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem alphaRepsR_cand : allR (fun α => memR α candR) alphaRepsR = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem candAll_true : candAll candR candW = true := by
  quickRfl

theorem candR_check_true : candR_check = true :=
  decide_eq_true (craw_of candR_swap alphaRepsR_cand candAll_true)

end CertificateChecks.KernelTwoHSLe4
