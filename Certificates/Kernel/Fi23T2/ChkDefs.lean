module

public import Certificates.Kernel.Fi23S.ChkDefs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Fi23T2.D "Certificates/Kernel/Fi23T2/data/t2.json.gz" 209268 14074518919093463083
  (S : List (List (List Nat))) (B : List Nat) (C : List (List Nat))

namespace CFSG.KD.Fi23T2

open CFSG.KC.Enum CFSG.KD.Fi23S

@[expose] noncomputable def gL (i x : Nat) : Nat :=
  gK (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)) x

@[expose] noncomputable def cjL (u i p : Nat) : Nat :=
  nIf(Nat.blt u (nat_lit 42), LS u (gL i (LS (Nat.xor u (nat_lit 1)) p)),
    strictN (Nat.sub u (nat_lit 42)) fun v =>
      strictN (Nat.div v (nat_lit 42)) fun a => strictN (Nat.mod v (nat_lit 42)) fun b =>
        LS a (LS b (gL i (LS (Nat.xor b (nat_lit 1)) (LS (Nat.xor a (nat_lit 1)) p)))))

@[expose] noncomputable def kyL (i u : Nat) : Nat :=
  Nat.lor (cjL u i (nat_lit 0)) (Nat.shiftLeft (cjL u i (nat_lit 2)) (nat_lit 15))

@[expose] noncomputable def neAll (f : Nat → Nat) (k : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Bool.not (Nat.beq k (f b)), ih)) l

@[expose] noncomputable def distK (f : Nat → Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => bAnd(strictB (f a) fun k => neAll f k t, ih)) l

@[expose] noncomputable def codesOK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun u _ ih => bAnd(Nat.blt u (nat_lit 1806), ih)) l

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def wOK (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun i t _ =>
    List.rec (motive := fun _ => Bool) false (fun tag us _ =>
      bIf(Nat.beq tag (nat_lit 0), Nat.beq (lenK us) (nat_lit 0),
        bAnd(Nat.beq tag (nat_lit 1), bAnd(Nat.beq (lenK us) (nat_lit 9),
          bAnd(codesOK us, distK (kyL i) us))))) t) e

@[expose] noncomputable def hd (e : List Nat) : Nat := List.getD e (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def memH (i : Nat) (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e _ ih => bIf(Nat.beq (hd e) i, true, ih)) L

@[expose] noncomputable def covK (L : List (List Nat)) (lo len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add lo d) fun i =>
    strictB (code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511))) fun c =>
      bIf(Nat.blt c (nat_lit 2), true, memH i L)

@[expose] noncomputable def entsK (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(wOK e, ih)) L

@[expose] noncomputable def slF (s : Nat) : Bool :=
  bAnd(covK (List.getD D.S s []) (Nat.mul s (nat_lit 16384)) (nat_lit 16384),
    entsK (List.getD D.S s []))

@[expose] noncomputable def largeOf (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun e _ ih => Bool.rec (motive := fun _ => List Nat) ih (hd e :: ih)
      (Nat.beq (List.getD e (nat_lit 1) (nat_lit 1)) (nat_lit 0))) L

@[expose] noncomputable def large : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun sl _ ih => largeOf sl ++ ih) D.S

@[expose] noncomputable def commK (a b : Nat) : Bool :=
  allN (nat_lit 6) fun x => Nat.beq (gL a (gL b x)) (gL b (gL a x))

@[expose] noncomputable def rcK : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(commK a b, ih2)) t, ih)) large

@[expose] noncomputable def subP (l : List Nat) (s x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun a _ ih s x => strictN (ih (Nat.shiftRight s (nat_lit 1)) x) fun y =>
      nIf(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1), gL a y, y)) l s x

@[expose] noncomputable def subKey (s : Nat) : Nat :=
  Nat.lor (subP D.B s (nat_lit 0)) (Nat.shiftLeft (subP D.B s (nat_lit 2)) (nat_lit 15))

@[expose] noncomputable def bK : Bool :=
  bAnd(Nat.beq (lenK D.B) (nat_lit 7), distK subKey (List.range 128))

@[expose] noncomputable def conjIn (t y : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z _ ih => bIf(allN (nat_lit 6) fun x => Nat.beq (LS t (gL y x)) (gL z (LS t x)), true, ih))
    l

@[expose] noncomputable def clK (l : List Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) (lenK l), bAnd(Nat.ble (lenK l) (nat_lit 8),
    List.rec (motive := fun _ => Bool) true
      (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
        bAnd(allN (nat_lit 42) fun t => conjIn t y l, ih))) l))

@[expose] noncomputable def cK : Bool :=
  bAnd(Nat.beq (lenK D.C) (nat_lit 7),
    allN (nat_lit 7) fun r => strictB (List.getD D.B r (nat_lit 0)) fun b =>
      bAnd(Nat.beq (hd (List.getD D.C r [])) b, bAnd(Nat.blt b (nat_lit 262144),
      bAnd(allN (nat_lit 6) (fun x => Nat.beq (gL b (gL b x)) x),
      bAnd(Bool.not (allN (nat_lit 6) fun x => Nat.beq (gL b x) x),
        clK (List.getD D.C r []))))))

end CFSG.KD.Fi23T2

end
