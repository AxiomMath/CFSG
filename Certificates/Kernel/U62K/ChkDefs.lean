module

public import Certificates.Kernel.Fi23T2.ChkDefs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.U62K.D "Certificates/Kernel/U62K/data/u62.json.gz" 216219 10072230031785334209
  (S : List (List (List Nat))) (B : List Nat) (K : List Nat) (P : List Nat)
  (C : List (List Nat)) (O : List Nat)

namespace CFSG.KD.U62K

open CFSG.KC.Enum CFSG.KD.Fi23S CFSG.KD.Fi23T2

@[expose] noncomputable def wPn (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih c x => nIf(Nat.beq c (nat_lit 0), x,
      strictN (ih (Nat.shiftRight c (nat_lit 6)) x) fun y =>
        LS (Nat.sub (Nat.land c (nat_lit 63)) (nat_lit 1)) y)) n

@[expose] noncomputable def wIn (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih c x => nIf(Nat.beq c (nat_lit 0), x,
      strictN (LS (Nat.xor (Nat.sub (Nat.land c (nat_lit 63)) (nat_lit 1)) (nat_lit 1)) x) fun y =>
        ih (Nat.shiftRight c (nat_lit 6)) y)) n

@[expose] noncomputable def vWn (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c (nat_lit 0))
    (fun _ ih c => bIf(Nat.beq c (nat_lit 0), true,
      bAnd(Nat.ble (nat_lit 1) (Nat.land c (nat_lit 63)),
        bAnd(Nat.ble (Nat.land c (nat_lit 63)) (nat_lit 42), ih (Nat.shiftRight c (nat_lit 6)))))) n

@[expose] noncomputable def wP (c x : Nat) : Nat := wPn (nat_lit 16) c x
@[expose] noncomputable def wI (c x : Nat) : Nat := wIn (nat_lit 16) c x
@[expose] noncomputable def vW (c : Nat) : Bool := vWn (nat_lit 16) c

@[expose] noncomputable def qq : Nat := nat_lit 14566

@[expose] noncomputable def okW (c : Nat) : Bool := bAnd(vW c, Nat.beq (wP c qq) qq)

@[expose] noncomputable def cj (c i p : Nat) : Nat := wP c (gL i (wI c p))

@[expose] noncomputable def cjI (c i p : Nat) : Nat := wI c (gL i (wP c p))

@[expose] noncomputable def kyW (i c : Nat) : Nat :=
  Nat.lor (cj c i (nat_lit 0)) (Nat.shiftLeft (cj c i (nat_lit 2)) (nat_lit 15))

@[expose] noncomputable def incK (f : Nat → Nat) (a : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih a => strictB (f b) fun k => bAnd(Nat.blt a k, ih k)) l a

@[expose] noncomputable def allL (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(f b, ih)) l

@[expose] noncomputable def inE (i m : Nat) : Bool :=
  bAnd(Nat.blt m (nat_lit 2048), allN (nat_lit 6) fun p => Nat.beq (gL i p) (subP D.B m p))

@[expose] noncomputable def wOK (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun i t _ =>
    List.rec (motive := fun _ => Bool) false (fun tag us _ =>
      bIf(Nat.beq tag (nat_lit 0),
        List.rec (motive := fun _ => Bool) false
          (fun m r _ => bAnd(Nat.beq (lenK r) (nat_lit 0), inE i m)) us,
        bAnd(Nat.beq tag (nat_lit 1), bAnd(Nat.beq (lenK us) (nat_lit 9),
          bAnd(allL okW us, incK (kyW i) (nat_lit 0) us))))) t) e

@[expose] noncomputable def covW (L : List (List Nat)) (lo len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add lo d) fun i =>
    strictB (code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511))) fun c =>
      bIf(Nat.blt c (nat_lit 2), true, bIf(Nat.beq (gL i qq) qq, memH i L, true))

@[expose] noncomputable def entsW (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(wOK e, ih)) L

@[expose] noncomputable def slF (s : Nat) : Bool :=
  bAnd(covW (List.getD D.S s []) (Nat.mul s (nat_lit 16384)) (nat_lit 16384),
    entsW (List.getD D.S s []))

@[expose] noncomputable def sw (u : Nat) : Nat :=
  strictN (Nat.mod u (nat_lit 42)) fun l =>
    strictN (nIf(Nat.blt u (nat_lit 42), Nat.succ l,
      Nat.add (nat_lit 3) (Nat.shiftLeft (Nat.succ l) (nat_lit 6)))) fun b =>
    nIf(Nat.beq (wP b qq) qq, b,
      Nat.add b (Nat.shiftLeft (nat_lit 4)
        (nIf(Nat.blt u (nat_lit 42), nat_lit 6, nat_lit 12))))

@[expose] noncomputable def invQ (i : Nat) : Bool :=
  bAnd(Nat.blt i (nat_lit 262144), bAnd(Nat.beq (gL i qq) qq,
    allN (nat_lit 6) fun p => Nat.beq (gL i (gL i p)) p))

@[expose] noncomputable def findL (f : Nat → Nat) (l : List Nat) : Bool :=
  strictB (f (nat_lit 0)) fun a =>
    List.rec (motive := fun _ => Bool) false
      (fun z _ ih => bIf(bAnd(Nat.beq (gL z (nat_lit 0)) a,
        allN (nat_lit 6) fun p => Nat.beq (gL z p) (f p)), true, ih)) l

@[expose] noncomputable def clW (l : List Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) (lenK l), bAnd(Nat.ble (lenK l) (nat_lit 8),
    List.rec (motive := fun _ => Bool) true
      (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
        bAnd(allN (nat_lit 84) fun u => strictB (sw u) fun c =>
          bAnd(findL (fun p => cj c y p) l, findL (fun p => cjI c y p) l), ih))) l))

@[expose] noncomputable def clF (m : Nat) : Bool :=
  strictB (List.getD D.P m (nat_lit 0)) fun b =>
    bAnd(Nat.beq (lenK D.P) (nat_lit 3), bAnd(Nat.beq (lenK D.C) (nat_lit 3),
    bAnd(Nat.beq (hd (List.getD D.C m [])) b, bAnd(invQ b,
    bAnd(Bool.not (allN (nat_lit 6) fun x => Nat.beq (gL b x) x),
      clW (List.getD D.C m []))))))

@[expose] noncomputable def commK (a b : Nat) : Bool :=
  allN (nat_lit 6) fun x => Nat.beq (gL a (gL b x)) (gL b (gL a x))

@[expose] noncomputable def pwK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => bAnd(allL (commK a) t, ih)) l

@[expose] noncomputable def bK : Bool :=
  bAnd(Nat.beq (lenK D.B) (nat_lit 11), bAnd(allL invQ D.B, pwK D.B))

@[expose] noncomputable def subKey (m : Nat) : Nat :=
  Nat.lor (subP D.B m (nat_lit 0)) (Nat.shiftLeft (subP D.B m (nat_lit 2)) (nat_lit 15))

@[expose] noncomputable def kK : Bool :=
  bAnd(Nat.beq (lenK D.K) (nat_lit 2048),
    bAnd(allL (fun m => Nat.blt m (nat_lit 2048)) D.K, incK subKey (nat_lit 0) D.K))

@[expose] noncomputable def keyO (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y _ ih => Nat.lor (Nat.shiftLeft ih (nat_lit 30)) (kyW y c)) D.P

@[expose] noncomputable def oK : Bool :=
  bAnd(Nat.beq (lenK D.O) (nat_lit 64), bAnd(allL okW D.O, incK keyO (nat_lit 0) D.O))

end CFSG.KD.U62K

end
