module

public import Certificates.Kernel.MonsterB.Fischer3067Orb
public import Certificates.Kernel.MonsterB.Fischer3067Chk
public import Certificates.Kernel.MonsterB.Fischer3066
public import CFSG.Certificates.Kernel.MonsterB.FischerBTSound
public import CFSG.Certificates.Kernel.MonsterB.FischerPackSound

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Sporadic.SmallF2.Native
  CFSG.KC.FischerK CFSG.KC.FischerB CFSG.KC.FischerE CFSG.KLie.CT

theorem vecMulN_nil (d v : Nat) : vecMulN d #[] v = 0 := by
  have key : ∀ (l : List Nat) (a : Nat),
      l.foldl (fun acc j => if v.testBit j then acc ^^^ ((#[] : Array Nat)[j]?.getD 0) else acc) a
        = a := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons j l ih =>
      intro a
      rw [List.foldl_cons, ih]
      simp
  exact key _ 0

theorem fColArr_size {k : Nat} (hk : k < 12) : (fColArr[k]!).size = 78 := by
  have h := CertificateChecks.KernelMonB.Fischer3066.kShape
  unfold fShapeCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  have hk' : k < fColArr.size := by rw [h.1]; exact hk
  rw [getElem!_pos fColArr k hk']
  exact h.2 k hk'

theorem vecMulN_fCol (k v : Nat) : vecMulN 78 (fColArr[k]!) v = vecMulL (fColArr[k]!).toList v := by
  by_cases hk : k < 12
  · exact vecMulN_eq (fColArr_size hk) v
  · have hs : ¬ k < fColArr.size := by
      have h := CertificateChecks.KernelMonB.Fischer3066.kShape
      unfold fShapeCheck at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1]
      exact hk
    rw [getElem!_neg fColArr k hs]
    change vecMulN 78 #[] v = vecMulL [] v
    rw [vecMulN_nil]
    rfl

theorem forIn_loopB {α β : Type} (R : α → β → Prop) (n : Nat) (f : Nat → α → Id (ForInStep α))
    (g : Nat → β → β) (a : α) (b : β) (h0 : R a b)
    (hs : ∀ i < n, ∀ a b, R a b → ∃ a', f i a = ForInStep.yield a' ∧ R a' (g i b)) :
    R (forIn [:n] a f) (loopB n g b) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have key : ∀ (k i : Nat), i + k ≤ n → ∀ a b, R a b →
      R (forIn (List.range' i k) a f)
        (Nat.rec (motive := fun _ => Nat → β → β) (fun _ b => b)
          (fun _ ih i b => ih (Nat.succ i) (g i b)) k i b) := by
    intro k
    induction k with
    | zero => intro _ _ a b h; exact h
    | succ k ih =>
      intro i hi a b h
      obtain ⟨a', hf, h'⟩ := hs i (by omega) a b h
      rw [List.range'_succ, List.forIn_cons, hf]
      exact ih (i + 1) (by omega) a' (g i b) h'
  exact key n 0 (by omega) a b h0

theorem vecMulL_zero : ∀ (R : List Nat), vecMulL R 0 = 0
  | [] => rfl
  | r :: R => by
    change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 r (Nat.beq (Nat.land 0 1) 1))
      (vecMulL R (Nat.shiftRight 0 1)) = 0
    have h : Nat.shiftRight 0 1 = 0 := rfl
    have h2 : Nat.land 0 1 = 0 := Nat.zero_and 1
    rw [h, vecMulL_zero R, h2]
    exact Nat.zero_xor 0

theorem vecMulL_take : ∀ (R : List Nat) (n v : Nat), v < 2 ^ n → vecMulL (R.take n) v = vecMulL R v
  | [], n, v, _ => by rw [List.take_nil]
  | r :: R, 0, v, hv => by
    have : v = 0 := by simpa using hv
    subst this
    rw [List.take_zero, vecMulL_zero, vecMulL_zero]
  | r :: R, n + 1, v, hv => by
    rw [List.take_succ_cons]
    change Nat.xor _ (vecMulL (R.take n) (Nat.shiftRight v 1)) =
      Nat.xor _ (vecMulL R (Nat.shiftRight v 1))
    rw [vecMulL_take R n _ (by
      change v >>> 1 < 2 ^ n
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      rw [Nat.pow_succ] at hv
      omega)]

theorem mulB_eq (k u : Nat) : mulB k u = vecMulL (fColArr[k]!).toList u := by
  unfold mulB
  by_cases h : u < 2048
  · have hb : Nat.blt u 2048 = true := decide_eq_true h
    rw [hb]
    exact vecMulL_take _ 11 u (by omega)
  · have hb : Nat.blt u 2048 = false := by
      exact decide_eq_false h
    rw [hb]

theorem frontB_append (F B : List Nat) :
    frontB F B ++ (backB F B).reverse = F ++ B.reverse := by
  cases F <;> simp [frontB, backB]

theorem frontB_headD (F B : List Nat) :
    (frontB F B ++ (backB F B).reverse).headD 0 = (frontB F B).headD 0 := by
  cases F <;> simp [frontB, backB]

theorem frontB_tail (F B : List Nat) :
    (frontB F B ++ (backB F B).reverse).tail = (frontB F B).tail ++ (backB F B).reverse := by
  cases F <;> simp [frontB, backB]

theorem arr_get_drop (q : Array Nat) (h : Nat) (hh : h < q.size) :
    q[h]! = (q.toList.drop h).headD 0 := by
  rw [getElem!_pos q h hh]
  have : h < q.toList.length := by simpa using hh
  rw [List.drop_eq_getElem_cons this]
  simp

def ROut (a : Array Nat × Array Nat × Array Nat × Array Nat × Nat) (b : SOB) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2 = b.2.2.2.2

def RMid (a : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Nat) (b : SHB) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2.1.toList.drop a.2.2.2.2.2 = b.2.2.2.2.1 ++ b.2.2.2.2.2.1.reverse ∧
    b.2.2.2.2.2.2.1 = a.2.2.2.2.1.size ∧ a.2.2.2.2.2 = b.2.2.2.2.2.2.2 ∧
    a.2.2.2.2.2 ≤ a.2.2.2.2.1.size

def RIn (h : Nat) (Ft : List Nat) (a : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat)
    (b : SKB) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2.toList.drop (h + 1) = Ft ++ b.2.2.2.2.1.reverse ∧ b.2.2.2.2.2 = a.2.2.2.2.size ∧
    h + 1 ≤ a.2.2.2.2.size

theorem run4_1 {A B C D E : Type} (X : Id (A × B × C × D × E)) :
    (Id.run (do let r ← X; pure (r.1, r.2.1, r.2.2.1, r.2.2.2.1))).1 = X.1 := rfl
theorem run4_2 {A B C D E : Type} (X : Id (A × B × C × D × E)) :
    (Id.run (do let r ← X; pure (r.1, r.2.1, r.2.2.1, r.2.2.2.1))).2.1 = X.2.1 := rfl
theorem run4_3 {A B C D E : Type} (X : Id (A × B × C × D × E)) :
    (Id.run (do let r ← X; pure (r.1, r.2.1, r.2.2.1, r.2.2.2.1))).2.2.1 = X.2.2.1 := rfl
theorem run4_4 {A B C D E : Type} (X : Id (A × B × C × D × E)) :
    (Id.run (do let r ← X; pure (r.1, r.2.1, r.2.2.1, r.2.2.2.1))).2.2.2 = X.2.2.2.1 := rfl

theorem stepKB_pos {t u k : Nat} {I D P G : BT} {Bk : List Nat} {qn : Nat}
    (hc : (decide (vecMulL (fColArr[k]!).toList u < 2048) &&
      getT I (vecMulL (fColArr[k]!).toList u) == 2048) = true) :
    stepKB t u k (I, D, P, G, Bk, qn) =
      (setT I (vecMulL (fColArr[k]!).toList u) t,
        setT D (vecMulL (fColArr[k]!).toList u) (getT D u + 1),
        setT P (vecMulL (fColArr[k]!).toList u) u, setT G (vecMulL (fColArr[k]!).toList u) k,
        vecMulL (fColArr[k]!).toList u :: Bk, qn + 1) := by
  unfold stepKB
  rw [mulB_eq]
  rw [Bool.and_eq_true, decide_eq_true_eq] at hc
  have h1 : Nat.blt (vecMulL (fColArr[k]!).toList u) 2048 = true := decide_eq_true hc.1
  have h2 : Nat.beq (getT I (vecMulL (fColArr[k]!).toList u)) 2048 = true := hc.2
  dsimp only
  rw [h1]
  dsimp only
  rw [h2]

theorem stepKB_neg {t u k : Nat} {I D P G : BT} {Bk : List Nat} {qn : Nat}
    (hc : ¬ (decide (vecMulL (fColArr[k]!).toList u < 2048) &&
      getT I (vecMulL (fColArr[k]!).toList u) == 2048) = true) :
    stepKB t u k (I, D, P, G, Bk, qn) = (I, D, P, G, Bk, qn) := by
  unfold stepKB
  rw [mulB_eq]
  dsimp only
  cases h1 : Nat.blt (vecMulL (fColArr[k]!).toList u) 2048
  · rfl
  · have h2 : Nat.beq (getT I (vecMulL (fColArr[k]!).toList u)) 2048 = false := by
      have h1' : vecMulL (fColArr[k]!).toList u < 2048 := Nat.le_of_ble_eq_true h1
      cases h3 : Nat.beq (getT I (vecMulL (fColArr[k]!).toList u)) 2048
      · rfl
      · exact absurd (by rw [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1', h3⟩) hc
    dsimp only
    rw [h2]

theorem stepHB_pos {t i : Nat} {I D P G : BT} {F Bk : List Nat} {qn h : Nat} (hc : h < qn) :
    stepHB t i (I, D, P, G, F, Bk, qn, h) =
      finHB (I, D, P, G, F, Bk, qn, h) (loopB 2 (stepKB t ((frontB F Bk).headD 0))
        (I, D, P, G, backB F Bk, qn)) := by
  unfold stepHB
  have hb : Nat.blt h qn = true := decide_eq_true hc
  dsimp only
  rw [hb]

theorem stepHB_neg {t i : Nat} {I D P G : BT} {F Bk : List Nat} {qn h : Nat} (hc : ¬ h < qn) :
    stepHB t i (I, D, P, G, F, Bk, qn, h) = (I, D, P, G, F, Bk, qn, h) := by
  unfold stepHB
  have hb : Nat.blt h qn = false := decide_eq_false hc
  dsimp only
  rw [hb]

theorem stepOB_pos {s t : Nat} {I D P G : BT} (hc : (getT I s == 2048) = true) :
    stepOB s (I, D, P, G, t) =
      finOB t (loopB 2048 (stepHB t) (setT I s t, D, P, G, [s], [], 1, 0)) := by
  unfold stepOB
  dsimp only
  rw [show Nat.beq (getT I s) 2048 = true from hc]

theorem stepOB_neg {s t : Nat} {I D P G : BT} (hc : ¬ (getT I s == 2048) = true) :
    stepOB s (I, D, P, G, t) = (I, D, P, G, t) := by
  unfold stepOB
  dsimp only
  rw [show Nat.beq (getT I s) 2048 = false from Bool.eq_false_iff.2 hc]

theorem out_of {x : Array Nat × Array Nat × Array Nat × Array Nat × Nat} {y : SOB}
    (h : ROut x y) : RArr x.1 y.1 ∧ RArr x.2.1 y.2.1 ∧ RArr x.2.2.1 y.2.2.1 ∧
      RArr x.2.2.2.1 y.2.2.2.1 := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem tup_1 (y : SOB) : (orbFinB y).1 = y.1 := rfl
theorem tup_2 (y : SOB) : (orbFinB y).2.1 = y.2.1 := rfl
theorem tup_3 (y : SOB) : (orbFinB y).2.2.1 = y.2.2.1 := rfl
theorem tup_4 (y : SOB) : (orbFinB y).2.2.2 = y.2.2.2.1 := rfl

theorem mid_of {x : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Nat} {y : SHB}
    (t : Nat) (h : RMid x y) :
    ROut (x.1, x.2.1, x.2.2.1, x.2.2.2.1, t + 1) (finOB t y) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

theorem in_of {x : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat} {y : SKB}
    {h : Nat} {Ft : List Nat} (S : SHB) (hS : S.2.2.2.2.2.2.2 = h)
    (hF : List.tail (frontB S.2.2.2.2.1 S.2.2.2.2.2.1) = Ft) (hR : RIn h Ft x y) :
    RMid (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, h + 1) (finHB S y) := by
  obtain ⟨hI, hD, hP, hG, hq, hqn, hle⟩ := hR
  refine ⟨hI, hD, hP, hG, ?_, hqn, ?_, hle⟩
  · show _ = List.tail (frontB S.2.2.2.2.1 S.2.2.2.2.2.1) ++ _
    rw [hF]; exact hq
  · show h + 1 = Nat.succ S.2.2.2.2.2.2.2
    rw [hS]

theorem orbitData_rel : RArr orbitData.1 orbitDataB.1 ∧ RArr orbitData.2.1 orbitDataB.2.1 ∧
    RArr orbitData.2.2.1 orbitDataB.2.2.1 ∧ RArr orbitData.2.2.2 orbitDataB.2.2.2 := by
  rw [orbitData, orbitDataB, run4_1, run4_2, run4_3, run4_4, tup_1, tup_2, tup_3, tup_4, orbRunB]
  refine out_of (forIn_loopB ROut 2048 _ stepOB _ _
    ⟨rArr_replicate 2048, rArr_replicate 0, rArr_replicate 0, rArr_replicate 0, rfl⟩ ?_)
  rintro s - ⟨idx, dist, par, gen, t⟩ ⟨IDX, DIST, PAR, GEN, t'⟩ ⟨hI, hD, hP, hG, ht⟩
  dsimp only at hI hD hP hG ht
  subst ht
  dsimp only
  rw [rArr_get hI s]
  by_cases hc : (getT IDX s == 2048) = true
  · rw [if_pos hc, stepOB_pos hc]
    refine ⟨_, rfl, mid_of t (forIn_loopB RMid 2048 _ (stepHB t) _ _
      ⟨rArr_set hI s t, hD, hP, hG, rfl, rfl, rfl, by simp⟩ ?_)⟩
    rintro - - ⟨idx, dist, par, gen, queue, h⟩ ⟨IDX, DIST, PAR, GEN, F, Bk, qn, h'⟩
      ⟨hI, hD, hP, hG, hq, hqn, hh, hle⟩
    dsimp only at hI hD hP hG hq hqn hh hle
    subst hqn hh
    dsimp only
    by_cases hc2 : h < queue.size
    · rw [if_pos hc2, stepHB_pos hc2]
      have hu : queue[h]! = (frontB F Bk).headD 0 := by
        rw [arr_get_drop queue h hc2, hq, ← frontB_append, frontB_headD]
      rw [hu]
      refine ⟨_, rfl, in_of _ rfl rfl (forIn_loopB (RIn h (frontB F Bk).tail) 2 _ _ _ _
        ⟨hI, hD, hP, hG, ?_, rfl, hc2⟩ ?_)⟩
      · rw [← List.tail_drop, hq, ← frontB_append, frontB_tail]
      rintro k - ⟨idx, dist, par, gen, q2⟩ ⟨IDX, DIST, PAR, GEN, Bk2, qn⟩
        ⟨hI, hD, hP, hG, hq2, hqn, hle2⟩
      dsimp only at hI hD hP hG hq2 hqn hle2
      subst hqn
      dsimp only
      rw [vecMulN_fCol, rArr_get hI, rArr_get hD]
      by_cases hc3 : (decide (vecMulL (fColArr[k]!).toList ((frontB F Bk).headD 0) < 2048) &&
          getT IDX (vecMulL (fColArr[k]!).toList ((frontB F Bk).headD 0)) == 2048) = true
      · rw [if_pos hc3, stepKB_pos hc3]
        refine ⟨_, rfl, rArr_set hI _ _, rArr_set hD _ _, rArr_set hP _ _, rArr_set hG _ _, ?_, ?_, ?_⟩
        · dsimp only
          rw [Array.toList_push, List.drop_append_of_le_length (by simpa using hle2), hq2,
            List.reverse_cons, List.append_assoc]
        · simp
        · simp; omega
      · rw [if_neg hc3, stepKB_neg hc3]
        exact ⟨_, rfl, hI, hD, hP, hG, hq2, rfl, hle2⟩
    · rw [if_neg hc2, stepHB_neg hc2]
      exact ⟨_, rfl, hI, hD, hP, hG, hq, rfl, rfl, hle⟩
  · rw [if_neg hc, stepOB_neg hc]
    exact ⟨_, rfl, hI, hD, hP, hG, rfl⟩

theorem orb_packed {a : Array ℕ} {T : BT} (h : RArr a T) {i : Nat} (hi : i < 4)
    (hk : ∀ m < 2048, getT T m = fget (FD.ORB[i]!) m 11) (m : Nat) :
    a[m]! = fget (FD.ORB[i]!) m 11 := by
  rw [rArr_get h]
  by_cases hm : m < 2048
  · exact hk m hm
  · have hb := kOrbB
    unfold orbBound at hb
    rw [List.all_eq_true] at hb
    have hlt := hb i (List.mem_range.2 hi)
    rw [decide_eq_true_eq] at hlt
    rw [getT_eq, if_neg hm, fget_big hlt (by omega)]

theorem orb_facts : ∀ m, orbIdx m = oIdx m ∧ orbDist m = oDist m ∧ orbPar m = oPar m ∧
    orbGen m = oGen m := by
  have h := kOrb
  obtain ⟨hI, hD, hP, hG⟩ := orbitData_rel
  generalize orbitDataB = D at h hI hD hP hG
  obtain ⟨a, b, c, d⟩ := D
  dsimp only at hI hD hP hG
  have hall := allN_true' (n := 2048) (f := fun m => getT a m == fget (FD.ORB[0]!) m 11 &&
    getT b m == fget (FD.ORB[1]!) m 11 && getT c m == fget (FD.ORB[2]!) m 11 &&
    getT d m == fget (FD.ORB[3]!) m 11) h
  intro m
  unfold orbIdx orbDist orbPar orbGen oIdx oDist oPar oGen
  refine ⟨orb_packed hI (i := 0) (by omega) (fun m hm => ?_) m,
    orb_packed hD (i := 1) (by omega) (fun m hm => ?_) m,
    orb_packed hP (i := 2) (by omega) (fun m hm => ?_) m,
    orb_packed hG (i := 3) (by omega) (fun m hm => ?_) m⟩ <;>
  · have := hall m hm
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    simp only [this]
where
  allN_true' {f : Nat → Bool} {n : Nat} (h : allN n f = true) : ∀ i < n, f i = true := by
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      change Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) = true at h
      cases hf : f n
      · rw [hf] at h
        exact absurd h Bool.false_ne_true
      · rw [hf] at h
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ih h i hi
        · exact hf

theorem orbIdx_eq (m : Nat) : orbIdx m = oIdx m := (orb_facts m).1
theorem orbDist_eq (m : Nat) : orbDist m = oDist m := (orb_facts m).2.1
theorem orbPar_eq (m : Nat) : orbPar m = oPar m := (orb_facts m).2.2.1
theorem orbGen_eq (m : Nat) : orbGen m = oGen m := (orb_facts m).2.2.2

end CertificateChecks.KernelMonB.F3067

end
