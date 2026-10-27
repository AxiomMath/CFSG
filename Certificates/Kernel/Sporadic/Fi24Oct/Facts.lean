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

theorem oct_facts :
    (∀ i < 24, cP NW NT (wc i) 0 = nthO 0 pts i) ∧
    (∀ i < 24, ∀ j < 24, cP NW NT (dW (wc i)) (nthO 0 pts j) = nthO 0 pts j) ∧
    (∀ i j k l : Nat, i < j → k < l → j < 24 → l < 24 → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      cP NW NT (dW (wc i)) (cP NW NT (dW (wc j)) sep) ≠
        cP NW NT (dW (wc k)) (cP NW NT (dW (wc l)) sep)) ∧
    (∀ k < 2, ∀ i < 24, cP NW NT (nc k) (nthO 0 pts i) = nthO 0 pts (nthO 0 (perm k) i)) ∧
    (∀ x < 306936, cP NW NT (prodC ow) x = x) := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i j k l hij hkl hj hl hik hil hjk hjl => ?_,
    fun k hk i hi => ?_, prodOK_spec CFSG.KD.Fi24ThreeO.vn Ck.pd_t⟩
  · have := rootOK_spec Ck.rt_t _ (List.getElem_mem (l := we) (by rw [we_length]; exact hi))
    rwa [we_get i hi] at this
  · have := commOK_spec Ck.cm_t _ (List.getElem_mem (l := we) (by rw [we_length]; exact hi)) _
      (List.getElem_mem (l := we) (by rw [we_length]; exact hj))
    rwa [we_get i hi, we_get j hj] at this
  · have hd := pairsOK_spec Ck.pr_t hij hkl (by rw [we_length]; exact hj)
      (by rw [we_length]; exact hl) (by
        rw [we_get i (by omega), we_get j hj, we_get k (by omega), we_get l hl]
        exact ⟨fun e => hik (pts_inj i (by omega) k (by omega) e),
          fun e => hil (pts_inj i (by omega) l hl e), fun e => hjk (pts_inj j hj k (by omega) e),
          fun e => hjl (pts_inj j hj l hl e)⟩)
    rwa [we_get i (by omega), we_get j hj, we_get k (by omega), we_get l hl] at hd
  · have h0 : ∀ k < 2, nm k = true := by
      intro k hk
      interval_cases k
      · exact Ck.nm0_t
      · exact Ck.nm1_t
    exact normOK_spec (h0 k hk) _ (pq_eq k i hi)

end CFSG.KD.Fi24Oct

end
