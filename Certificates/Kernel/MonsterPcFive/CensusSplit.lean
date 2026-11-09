module

public import Certificates.Data.Kernel.MonsterPcFive.Census

public section

namespace CFSG.KC.MonPcFive

@[expose] def stepV (rep depth : List Nat) (nc dc c' w : Nat) (v' : V9) : Bool :=
  Nat.blt c' nc && Nat.blt (nthN depth c') dc &&
    (mulV (dec w) v').beq (mulV (dec (nthN rep c')) (dec w))

@[expose] def classV (rep depth : List Nat) (nc rc dc k a cl w : Nat) : Bool :=
  let r := dec rc
  bif k.beq 0 then memK rc repK
  else bif k.beq 1 then Nat.blt a 3 && stepV rep depth nc dc cl w (alphaW (autW a) r)
  else Nat.ble 2 a && Nat.blt a 5 && ord5 r && stepV rep depth nc dc cl w (powV r a)

theorem classW_eq (rep depth kind arg cls wit : List Nat) (nc c : Nat) :
    classW rep depth kind arg cls wit nc c = classV rep depth nc (nthN rep c) (nthN depth c)
      (nthN kind c) (nthN arg c) (nthN cls c) (nthN wit c) := rfl

@[expose] def fusL (rep depth : List Nat) (nc : Nat) :
    Nat → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → Bool
  | 0, _, _, _, _, _, _ => true
  | n + 1, rs, ds, ks, as, cs, ws =>
    classV rep depth nc (nthN rs 0) (nthN ds 0) (nthN ks 0) (nthN as 0) (nthN cs 0) (nthN ws 0) &&
      fusL rep depth nc n rs.tail ds.tail ks.tail as.tail cs.tail ws.tail

theorem nthN_drop : ∀ (lo : Nat) (l : List Nat) (c : Nat), nthN (l.drop lo) c = nthN l (lo + c)
  | 0, l, c => by rw [List.drop_zero, Nat.zero_add]
  | lo + 1, [], c => by simp [nthN]
  | lo + 1, a :: t, c => by
    rw [List.drop_succ_cons, nthN_drop lo t c, Nat.add_right_comm]
    rfl

theorem allBelow_of {f : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = true) → allBelow f n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨h n (Nat.lt_succ_self n), allBelow_of fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem fusL_sound (rep depth kind arg cls wit : List Nat) (nc : Nat) :
    ∀ (n lo : Nat), fusL rep depth nc n (rep.drop lo) (depth.drop lo) (kind.drop lo) (arg.drop lo)
      (cls.drop lo) (wit.drop lo) = true →
      ∀ c < n, classW rep depth kind arg cls wit nc (lo + c) = true
  | 0, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | n + 1, lo, h, c, hc => by
    simp only [fusL, Bool.and_eq_true] at h
    rcases c with _ | c
    · rw [classW_eq, ← nthN_drop lo rep 0, ← nthN_drop lo depth 0, ← nthN_drop lo kind 0,
        ← nthN_drop lo arg 0, ← nthN_drop lo cls 0, ← nthN_drop lo wit 0]
      exact h.1
    · simp only [List.tail_drop] at h
      have := fusL_sound rep depth kind arg cls wit nc n (lo + 1) h.2 c (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem fusW_of_fusL {rep depth kind arg cls wit : List Nat} {nc lo n : Nat}
    (h : fusL rep depth nc n (rep.drop lo) (depth.drop lo) (kind.drop lo) (arg.drop lo)
      (cls.drop lo) (wit.drop lo) = true) :
    fusW rep depth kind arg cls wit nc lo n = true :=
  allBelow_of (fusL_sound rep depth kind arg cls wit nc n lo h)

@[expose] def skipH : Nat → List Nat → List Nat
  | 0, hs => hs
  | n + 1, _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: hs => skipH n hs
  | _ + 1, hs => hs

@[expose] def skipP : Nat → List Nat → List Nat → List Nat
  | 0, _, ps => ps
  | n + 1, _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: m :: hs, ps => skipP n hs (ps.drop (ptCnt m))
  | _ + 1, _, ps => ps

theorem repsRun_split (rcs rep : List Nat) (nc n2 : Nat) :
    ∀ (r n1 : Nat) (hs ps : List Nat), repsRun rcs rep nc r n1 hs ps = true →
      repsRun rcs rep nc (r + n1) n2 (skipH n1 hs) (skipP n1 hs ps) = true →
      repsRun rcs rep nc r (n1 + n2) hs ps = true := by
  intro r n1 hs ps
  induction r, n1, hs, ps using repsRun.induct rcs with
  | case1 r hs ps =>
    intro _ h2
    simpa [skipH, skipP] using h2
  | case2 r n c0 c1 c2 c3 s0 s1 s2 s3 m hs ps ih =>
    intro h1 h2
    rw [show n.succ + n2 = (n + n2) + 1 by omega, repsRun]
    rw [repsRun, Bool.and_eq_true] at h1
    rw [Bool.and_eq_true]
    refine ⟨h1.1, ih h1.2 ?_⟩
    simp only [skipH, skipP] at h2
    rwa [show r + n.succ = r + 1 + n by omega] at h2
  | case3 r n hs ps h =>
    intro h1 _
    rw [repsRun.eq_3 _ _ _ _ _ _ _ h] at h1
    exact absurd h1 Bool.false_ne_true

end CFSG.KC.MonPcFive

end
