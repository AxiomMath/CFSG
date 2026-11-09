module

public import Certificates.Data.Kernel.He7222.Chain
public import Certificates.Data.Kernel.He7222.Cls
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain

@[expose] noncomputable def treeWC (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun j _ => Nat.beq j (lenS R))
    (fun t _ ih j seen => strictB (getS R j) (fun e =>
      strictB (Nat.land e m) (fun pt =>
      bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
      bAnd(bIf(Nat.beq j (nat_lit 0),
          bAnd(Nat.beq pt b, Nat.beq t idn),
          strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
          strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
            bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
              Nat.beq t (pcompC n w m (getS G g) (getS T par)))))))),
        strictB (Nat.succ j) (fun j' => ih j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))))

@[expose] noncomputable def treeKC (n w m idn : Nat) (G : List Nat) (b : Nat) (R T : List Nat) :
    Bool :=
  treeWC n w m idn G (lenS G) b R T T (nat_lit 0) (nat_lit 0)

theorem treeK_C (n w idn : Nat) (G : List Nat) (b : Nat) (R T : List Nat) :
    treeK n w (mask w) idn G b R T = treeKC n w (mask w) idn G b R T := by
  unfold treeKC treeWC
  simp only [CFSG.KS.PK.pcompC_eq]
  rfl

@[expose] noncomputable def invKC (n w m idn T TI : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight TI (Nat.mul n w)) (nat_lit 0),
    bAnd(Nat.blt (pg w m TI (nat_lit 0)) n, Nat.beq (pcompC n w m T TI) idn))

@[expose] noncomputable def invLKC (n w m idn : Nat) (T TI : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (lenS TI))
    (fun t _ ih j => bAnd(invKC n w m idn t (getS TI j), strictB (Nat.succ j) ih)) T (nat_lit 0)

theorem invLK_C (n w idn : Nat) (T TI : List Nat) :
    invLK n w (mask w) idn T TI = invLKC n w (mask w) idn T TI := by
  unfold invLKC invKC
  simp only [CFSG.KS.PK.pcompC_eq]
  rfl

@[expose] noncomputable def invFromC (n w m idn : Nat) (TI T : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (lenS TI))
    (fun t _ ih j => bAnd(invKC n w m idn t (getS TI j), strictB (Nat.succ j) ih)) T j

@[expose] noncomputable def invAllC (n w m idn : Nat) (TI T : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => bAnd(invKC n w m idn t (getS TI j), strictB (Nat.succ j) ih)) T j

theorem invLKC_from (n w m idn : Nat) (T TI : List Nat) :
    invLKC n w m idn T TI = invFromC n w m idn TI T 0 := rfl

theorem invFromC_cons (n w m idn : Nat) (TI : List Nat) (a : Nat) (A : List Nat) (j : Nat) :
    invFromC n w m idn TI (a :: A) j =
      bAnd(invKC n w m idn a (getS TI j), strictB (Nat.succ j) (invFromC n w m idn TI A)) := rfl

theorem invAllC_cons (n w m idn : Nat) (TI : List Nat) (a : Nat) (A : List Nat) (j : Nat) :
    invAllC n w m idn TI (a :: A) j =
      bAnd(invKC n w m idn a (getS TI j), strictB (Nat.succ j) (invAllC n w m idn TI A)) := rfl

theorem invFromC_append (n w m idn : Nat) (TI : List Nat) : ∀ (A B : List Nat) (j : Nat),
    invFromC n w m idn TI (A ++ B) j =
      (invAllC n w m idn TI A j && invFromC n w m idn TI B (j + A.length))
  | [], B, j => by
    show invFromC n w m idn TI B j = (true && invFromC n w m idn TI B (j + 0))
    rw [Nat.add_zero, Bool.true_and]
  | a :: A, B, j => by
    rw [List.cons_append, invFromC_cons, invAllC_cons, CFSG.KS.PF.strictB_eqP,
      CFSG.KS.PF.strictB_eqP, invFromC_append n w m idn TI A B (Nat.succ j), List.length_cons,
      show Nat.succ j + A.length = j + (A.length + 1) by omega]
    cases invKC n w m idn a (getS TI j) <;> rfl

@[expose] noncomputable def treeAllC (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun t _ ih j seen => strictB (getS R j) (fun e =>
      strictB (Nat.land e m) (fun pt =>
      bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
      bAnd(bIf(Nat.beq j (nat_lit 0),
          bAnd(Nat.beq pt b, Nat.beq t idn),
          strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
          strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
            bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
              Nat.beq t (pcompC n w m (getS G g) (getS T par)))))))),
        strictB (Nat.succ j) (fun j' => ih j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))))

@[expose] noncomputable def seenC (m : Nat) (R : List Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ _ ih j s => ih (Nat.succ j) (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.land (getS R j) m))))

theorem treeWC_cons (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) (t : Nat)
    (A : List Nat) (j seen : Nat) :
    treeWC n w m idn G k b R T (t :: A) j seen =
      strictB (getS R j) (fun e =>
        strictB (Nat.land e m) (fun pt =>
        bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
        bAnd(bIf(Nat.beq j (nat_lit 0),
            bAnd(Nat.beq pt b, Nat.beq t idn),
            strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
            strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
              bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
                Nat.beq t (pcompC n w m (getS G g) (getS T par)))))))),
          strictB (Nat.succ j) (fun j' => treeWC n w m idn G k b R T A j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))) := rfl

theorem treeAllC_cons (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) (t : Nat)
    (A : List Nat) (j seen : Nat) :
    treeAllC n w m idn G k b R T (t :: A) j seen =
      strictB (getS R j) (fun e =>
        strictB (Nat.land e m) (fun pt =>
        bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
        bAnd(bIf(Nat.beq j (nat_lit 0),
            bAnd(Nat.beq pt b, Nat.beq t idn),
            strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
            strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
              bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
                Nat.beq t (pcompC n w m (getS G g) (getS T par)))))))),
          strictB (Nat.succ j) (fun j' => treeAllC n w m idn G k b R T A j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))) := rfl

theorem seenC_cons (m : Nat) (R : List Nat) (t : Nat) (A : List Nat) (j s : Nat) :
    seenC m R (t :: A) j s =
      seenC m R A (Nat.succ j) (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.land (getS R j) m))) := rfl

theorem bool_rec2 (c1 c2 x y : Bool) :
    Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (x && y) c2) c1 =
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false x c2) c1 && y) := by
  cases c1 <;> cases c2 <;> rfl

theorem treeWC_append (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) :
    ∀ (A B : List Nat) (j seen : Nat),
    treeWC n w m idn G k b R T (A ++ B) j seen =
      (treeAllC n w m idn G k b R T A j seen &&
        treeWC n w m idn G k b R T B (j + A.length) (seenC m R A j seen))
  | [], B, j, seen => by
    show treeWC n w m idn G k b R T B j seen = (true && treeWC n w m idn G k b R T B (j + 0) seen)
    rw [Nat.add_zero, Bool.true_and]
  | t :: A, B, j, seen => by
    rw [List.cons_append, treeWC_cons, treeAllC_cons, seenC_cons]
    simp only [CFSG.KS.PF.strictB_eqP]
    rw [treeWC_append n w m idn G k b R T A B (Nat.succ j), List.length_cons,
      show Nat.succ j + A.length = j + (A.length + 1) by omega]
    exact bool_rec2 _ _ _ _

end CFSG.KD.He7222

end
