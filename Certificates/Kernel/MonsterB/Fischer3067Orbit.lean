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

def ROut (a : Array ℕ × Array ℕ × Array ℕ × Array ℕ × ℕ) (b : BT × BT × BT × BT × ℕ) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2 = b.2.2.2.2

def RMid (a : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ × ℕ)
    (b : BT × BT × BT × BT × Array ℕ × ℕ × ℕ) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2.1 = b.2.2.2.2.1 ∧ b.2.2.2.2.2.1 = a.2.2.2.2.1.size ∧ a.2.2.2.2.2 = b.2.2.2.2.2.2

def RIn (a : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ)
    (b : BT × BT × BT × BT × Array ℕ × ℕ) : Prop :=
  RArr a.1 b.1 ∧ RArr a.2.1 b.2.1 ∧ RArr a.2.2.1 b.2.2.1 ∧ RArr a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2 = b.2.2.2.2.1 ∧ b.2.2.2.2.2 = a.2.2.2.2.size

theorem out_of {x : Array ℕ × Array ℕ × Array ℕ × Array ℕ × ℕ} {y : BT × BT × BT × BT × ℕ}
    (h : ROut x y) : RArr x.1 y.1 ∧ RArr x.2.1 y.2.1 ∧ RArr x.2.2.1 y.2.2.1 ∧
      RArr x.2.2.2.1 y.2.2.2.1 := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem mid_of {x : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ × ℕ}
    {y : BT × BT × BT × BT × Array ℕ × ℕ × ℕ} (t : ℕ) (h : RMid x y) :
    ROut (x.1, x.2.1, x.2.2.1, x.2.2.2.1, t + 1) (y.1, y.2.1, y.2.2.1, y.2.2.2.1, t + 1) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

theorem in_of {x : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ}
    {y : BT × BT × BT × BT × Array ℕ × ℕ} (n : ℕ) (h : RIn x y) :
    RMid (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, n + 1)
      (y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2, n + 1) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, rfl⟩

theorem orbitData_rel : RArr orbitData.1 orbitDataB.1 ∧ RArr orbitData.2.1 orbitDataB.2.1 ∧
    RArr orbitData.2.2.1 orbitDataB.2.2.1 ∧ RArr orbitData.2.2.2 orbitDataB.2.2.2 := by
  unfold orbitData orbitDataB
  refine out_of (forIn_rel ROut 2048 _ _ _ _
    ⟨rArr_replicate 2048, rArr_replicate 0, rArr_replicate 0, rArr_replicate 0, rfl⟩ ?_)
  rintro s - ⟨idx, dist, par, gen, t⟩ ⟨IDX, DIST, PAR, GEN, t'⟩ ⟨hI, hD, hP, hG, ht⟩
  dsimp only at hI hD hP hG ht
  subst ht
  dsimp only
  rw [rArr_get hI s]
  by_cases hc : (getT IDX s == 2048) = true
  · rw [if_pos hc, if_pos hc]
    refine ⟨_, _, rfl, rfl, mid_of t (forIn_rel RMid 2048 _ _ _ _
      ⟨rArr_set hI s t, hD, hP, hG, rfl, rfl, rfl⟩ ?_)⟩
    rintro - - ⟨idx, dist, par, gen, queue, h⟩ ⟨IDX, DIST, PAR, GEN, queue', qn, h'⟩
      ⟨hI, hD, hP, hG, hq, hqn, hh⟩
    dsimp only at hI hD hP hG hq hqn hh
    subst hq hqn hh
    dsimp only
    by_cases hc2 : h < queue.size
    · rw [if_pos hc2, if_pos hc2]
      refine ⟨_, _, rfl, rfl, in_of h (forIn_rel RIn 2 _ _ _ _ ⟨hI, hD, hP, hG, rfl, rfl⟩ ?_)⟩
      rintro k - ⟨idx, dist, par, gen, q2⟩ ⟨IDX, DIST, PAR, GEN, q2', qn⟩
        ⟨hI, hD, hP, hG, hq, hqn⟩
      dsimp only at hI hD hP hG hq hqn
      subst hq hqn
      dsimp only
      rw [vecMulN_fCol, rArr_get hI, rArr_get hD]
      by_cases hc3 : (decide (vecMulL (fColArr[k]!).toList queue[h]! < 2048) &&
          getT IDX (vecMulL (fColArr[k]!).toList queue[h]!) == 2048) = true
      · rw [if_pos hc3, if_pos hc3]
        refine ⟨_, _, rfl, rfl, rArr_set hI _ _, rArr_set hD _ _, rArr_set hP _ _,
          rArr_set hG _ _, rfl, ?_⟩
        rw [Array.size_push]
      · rw [if_neg hc3, if_neg hc3]
        exact ⟨_, _, rfl, rfl, hI, hD, hP, hG, rfl, rfl⟩
    · rw [if_neg hc2, if_neg hc2]
      exact ⟨_, _, rfl, rfl, hI, hD, hP, hG, rfl, rfl, rfl⟩
  · rw [if_neg hc, if_neg hc]
    exact ⟨_, _, rfl, rfl, hI, hD, hP, hG, rfl⟩

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
