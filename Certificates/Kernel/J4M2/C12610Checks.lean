module

public import Certificates.Kernel.J4M2.C12611Checks
public import Certificates.Kernel.J4M2.C12610Snaps
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KC.J4Slp
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Sporadic.J4Schreier

@[expose] noncomputable def threeR : List Nat :=
  runK c rm one (threeProg.map instrCode) (initKN one A A B Bi 140)

@[expose] noncomputable def threeT (E EI G GI : List Nat) : Bool :=
  andB (Nat.beq (getN 0 E 0) one) (andB
    ((List.range 27).all fun k => (List.range 27).all fun l =>
      CFSG.KC.J4Slp.strictB (mulJ c rm (getN 0 E k) (getN 0 E l)) fun p =>
        (List.range 27).any fun m => Nat.beq p (getN 0 E m))
    (andB ((List.range 27).all fun k => (List.range 27).any fun m => Nat.beq (getN 0 EI k) (getN 0 E m))
      (andB ((List.range 27).all fun k => (List.range 27).all fun l =>
          orB (Nat.beq k l) (neK rm (getN 0 E k) (getN 0 E l)))
        ((List.range 27).all fun k => orB (Nat.beq k 0)
          (Nat.beq (mulJ c rm (mulJ c rm (getN 0 G k) (getN 0 E k)) (getN 0 GI k)) CE)))))

@[expose] noncomputable def colK (R : List Nat) (o i : Nat) : List Nat :=
  (List.range 27).map fun k => getN 0 R (2 * (o + k) + i)

@[expose] noncomputable def threeK (R : List Nat) : Bool :=
  forceB (colK R 70 0) fun E => forceB (colK R 70 1) fun EI =>
    forceB (colK R 110 0) fun G => forceB (colK R 110 1) fun GI => threeT E EI G GI

theorem c12610lt : threeProg.all (CFSG.Sporadic.GLQ.Instr.lt threeN) = true := by quickRfl

@[expose] noncomputable def thrP : List (List Nat) := threeProg.map instrCode

theorem threeR_eq : threeR = runK c rm one thrP (initKN one A A B Bi 140) := rfl

@[expose] noncomputable def eqL : List Nat → List Nat → Bool := fun a =>
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y t _ => Nat.beq x y && ih t) b) a

theorem eqL_eq : ∀ (a b : List Nat), eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | x :: a, y :: b, h => by
    have h' : (Nat.beq x y && eqL a b) = true := h
    rw [Bool.and_eq_true] at h'
    rw [Nat.eq_of_beq_eq_true h'.1, eqL_eq a b h'.2]

theorem forceL_id : ∀ (l : List Nat) (k : List Nat → List Nat), CFSG.KC.J4Slp.forceL l k = k l
  | [], _ => rfl
  | x :: l, k => by
    show CFSG.KC.J4Slp.strictL x (fun a => CFSG.KC.J4Slp.forceL l fun t => k (a :: t)) = _
    have hs : ∀ (y : Nat) (k' : Nat → List Nat), CFSG.KC.J4Slp.strictL y k' = k' y := fun y k' => by
      cases y <;> rfl
    rw [hs]
    exact forceL_id l fun t => k (x :: t)

theorem runK_append (c' rm' one' : Nat) : ∀ (p q : List (List Nat)) (R : List Nat),
    CFSG.KC.J4Slp.runK c' rm' one' (p ++ q) R = CFSG.KC.J4Slp.runK c' rm' one' q (CFSG.KC.J4Slp.runK c' rm' one' p R)
  | [], _, _ => rfl
  | code :: p, q, R => by
    show CFSG.KC.J4Slp.forceL (CFSG.KC.J4Slp.stepK c' rm' one' R code) (CFSG.KC.J4Slp.runK c' rm' one' (p ++ q)) =
      CFSG.KC.J4Slp.runK c' rm' one' q (CFSG.KC.J4Slp.forceL (CFSG.KC.J4Slp.stepK c' rm' one' R code) (CFSG.KC.J4Slp.runK c' rm' one' p))
    rw [forceL_id, forceL_id]
    exact runK_append c' rm' one' p q _

theorem split4 {α : Type} (L : List α) :
    ((L.take 615 ++ (L.drop 615).take 637) ++ (L.drop 1252).take 641) ++ L.drop 1893 = L := by
  have h1 : L.take 615 ++ (L.drop 615).take 637 = L.take 1252 := (List.take_add ..).symm
  have h2 : L.take 1252 ++ (L.drop 1252).take 641 = L.take 1893 := (List.take_add ..).symm
  rw [h1, h2, List.take_append_drop]

open CFSG.KD.J4C12610

theorem c12610p0 : eqL (runK c rm one (thrP.take 615) (initKN one A A B Bi 140)) S615 = true := by
  quickRfl

theorem c12610p1 : eqL (runK c rm one ((thrP.drop 615).take 637) S615) S1252 = true := by
  quickRfl

theorem c12610p2 : eqL (runK c rm one ((thrP.drop 1252).take 641) S1252) S1893 = true := by
  quickRfl

theorem c12610p3 : forceB (runK c rm one (thrP.drop 1893) S1893) threeK = true := by quickRfl

theorem c12610run : forceB threeR threeK = true := by
  rw [threeR_eq, ← split4 thrP, runK_append, runK_append, runK_append,
    eqL_eq _ _ c12610p0, eqL_eq _ _ c12610p1, eqL_eq _ _ c12610p2]
  exact c12610p3

end CertificateChecks.KernelJ4Gam

end
