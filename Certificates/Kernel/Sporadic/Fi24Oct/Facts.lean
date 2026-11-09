module

public import Certificates.Kernel.Sporadic.Fi24Oct.Checks
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24OctSound

public section

namespace CFSG.KD.Fi24Oct

open CFSG.KC CFSG.KC.Fi24Oct CFSG.KC.Fi24ThreeO CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Oct
  CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem we_length : we.length = 24 := by decide +kernel

theorem we_get : ∀ (i : Nat) (h : i < 24),
    we[i]'(by rw [we_length]; exact h) = (wc i, nthO 0 pts i) := by decide +kernel

theorem pts_length : pts.length = 24 := rfl

theorem nthO_eq : ∀ (l : List Nat) (i : Nat) (h : i < l.length), nthO 0 l i = l[i]
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => nthO_eq l i (by simpa using h)

theorem pts_inj : ∀ i < 24, ∀ j < 24, nthO 0 pts i = nthO 0 pts j → i = j := by decide +kernel

theorem perm_lt : ∀ k < 2, ∀ i < 24, nthO 0 (perm k) i < 24 := by decide +kernel

theorem pq_eq (k : Nat) : ∀ i < 24,
    (nthO 0 pts i, nthO 0 pts (nthO 0 (perm k) i)) ∈ pq k := by
  have key : ∀ (l : List Nat) (i₀ i : Nat) (h : i < l.length),
      (l[i], nthO 0 pts (nthO 0 (perm k) (i₀ + i))) ∈
        List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
          (fun p _ ih i => (p, nthO 0 pts (nthO 0 (perm k) i)) :: ih (Nat.succ i)) l i₀ := by
    intro l
    induction l with
    | nil => intro _ i h; exact absurd h (by simp)
    | cons p l ih =>
      intro i₀ i h
      cases i with
      | zero => exact List.mem_cons_self
      | succ i =>
        refine List.mem_cons_of_mem _ ?_
        have := ih (Nat.succ i₀) i (by simpa using h)
        rwa [show Nat.succ i₀ + i = i₀ + (i + 1) by omega] at this
  intro i hi
  have := key pts 0 i (by rw [pts_length]; exact hi)
  rw [Nat.zero_add, ← nthO_eq pts i (by rw [pts_length]; exact hi)] at this
  exact this

theorem commUp_spec : ∀ (l : List (List Nat × Nat)), commUp l = true →
    ∀ i j (hij : i < j) (hj : j < l.length),
      cP NW NT (dW (l[i]'(by omega)).1) (l[j]'hj).2 = (l[j]'hj).2
  | [], _, _, _, _, hj => absurd hj (by simp)
  | a :: t, h, i, j, hij, hj => by
    have hA : allL (fun b => Nat.beq (ptC NW NT (dW a.1) b.2) b.2) t = true ∧
        commUp t = true := by
      change andB (allL (fun b => Nat.beq (ptC NW NT (dW a.1) b.2) b.2) t) (commUp t) = true at h
      cases hx : allL (fun b => Nat.beq (ptC NW NT (dW a.1) b.2) b.2) t
      · rw [hx] at h
        exact absurd h Bool.false_ne_true
      · rw [hx] at h
        exact ⟨rfl, h⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    cases i with
    | zero =>
      have := allL_spec hA.1 _ (List.getElem_mem (l := t) (by simpa using hj))
      rw [← ptC_eq]
      exact Nat.eq_of_beq_eq_true this
    | succ i => exact commUp_spec t hA.2 i j (by omega) (by simpa using hj)

theorem wvo_length : (wvo.map fun e => (e.1, e.2.1)).length = 24 := by decide +kernel

theorem wvo_get : ∀ (x : Nat) (h : x < 24),
    (wvo.map fun e => (e.1, e.2.1))[x]'(by rw [wvo_length]; exact h) =
      (wc (nthO 0 ordO24 x), nthO 0 pts (nthO 0 ordO24 x)) := by decide +kernel

theorem ordO24_inj : ∀ x < 24, ∀ z < 24,
    nthO 0 pts (nthO 0 ordO24 x) = nthO 0 pts (nthO 0 ordO24 z) → x = z := by decide +kernel

theorem ordO24_pos : ∀ a < 24, nthO 0 ordO24 (nthO 0 posO24 a) = a ∧ nthO 0 posO24 a < 24 := by
  decide +kernel

theorem pr_ok : pairsOK NW NT sep (wvo.map fun e => (e.1, e.2.1)) = true :=
  pairsOK_of_R Ck.sv_t Ck.prR_t

theorem pd_ok : prodOK NW NT ow = true := by
  refine prodOK_of_planes (Nat.eq_of_beq_eq_true Ck.pdz_t) fun k hk => ?_
  have h : pdk k = true := by
    interval_cases k
    · exact Ck.pd0_t
    · exact Ck.pd1_t
    · exact Ck.pd2_t
    · exact Ck.pd3_t
    · exact Ck.pd4_t
    · exact Ck.pd5_t
    · exact Ck.pd6_t
    · exact Ck.pd7_t
    · exact Ck.pd8_t
    · exact Ck.pd9_t
    · exact Ck.pd10_t
    · exact Ck.pd11_t
    · exact Ck.pd12_t
    · exact Ck.pd13_t
    · exact Ck.pd14_t
    · exact Ck.pd15_t
    · exact Ck.pd16_t
    · exact Ck.pd17_t
  exact Nat.eq_of_beq_eq_true h

theorem oct_facts :
    (∀ i < 24, cP NW NT (wc i) 0 = nthO 0 pts i) ∧
    (∀ i < 24, ∀ j < 24, i < j → cP NW NT (dW (wc i)) (nthO 0 pts j) = nthO 0 pts j) ∧
    (∀ x y z w : Nat, x < y → z < w → y < 24 → w < 24 → x ≠ z → x ≠ w → y ≠ z → y ≠ w →
      cP NW NT (dW (wc (nthO 0 ordO24 x))) (cP NW NT (dW (wc (nthO 0 ordO24 y))) sep) ≠
        cP NW NT (dW (wc (nthO 0 ordO24 z))) (cP NW NT (dW (wc (nthO 0 ordO24 w))) sep)) ∧
    (∀ k < 2, ∀ i < 24, cP NW NT (nc k) (nthO 0 pts i) = nthO 0 pts (nthO 0 (perm k) i)) ∧
    (∀ x < 306936, cP NW NT (prodC ow) x = x) := by
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i j k l hij hkl hj hl hik hil hjk hjl => ?_,
    fun k hk i hi => ?_, prodOK_spec CFSG.KD.Fi24ThreeO.vn pd_ok⟩
  · have := rootOK_spec Ck.rt_t _ (List.getElem_mem (l := we) (by rw [we_length]; exact hi))
    rwa [we_get i hi] at this
  · have := commUp_spec we Ck.cm_t i j hij (by rw [we_length]; exact hj)
    rwa [we_get i hi, we_get j hj] at this
  · have hd := pairsOK_spec pr_ok hij hkl (by rw [wvo_length]; exact hj)
      (by rw [wvo_length]; exact hl) (by
        rw [wvo_get i (by omega), wvo_get j hj, wvo_get k (by omega), wvo_get l hl]
        exact ⟨fun e => hik (ordO24_inj i (by omega) k (by omega) e),
          fun e => hil (ordO24_inj i (by omega) l hl e), fun e => hjk (ordO24_inj j hj k (by omega) e),
          fun e => hjl (ordO24_inj j hj l hl e)⟩)
    rwa [wvo_get i (by omega), wvo_get j hj, wvo_get k (by omega), wvo_get l hl] at hd
  · have h0 : ∀ k < 2, nm k = true := by
      intro k hk
      interval_cases k
      · exact Ck.nm0_t
      · exact Ck.nm1_t
    exact normOK_spec (h0 k hk) _ (pq_eq k i hi)

end CFSG.KD.Fi24Oct

end
