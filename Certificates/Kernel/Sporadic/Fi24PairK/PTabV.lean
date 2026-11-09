module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.PTab
public import Certificates.Kernel.Sporadic.Fi24PairK.PcData

#kc_repo #kc_ktree CFSG.KD.Fi24PairK PTabV "Certificates/Kernel/Sporadic/Fi24PairK/data/ptabv.bin" 4096 4 66355200 6364333329985179294

public section

namespace CFSG.KD.Fi24PairK

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24NetPt

@[expose] noncomputable def PTVj (s c : Nat) : Nat := PTabV (Nat.add (Nat.mul s (nat_lit 600)) c)

@[expose] noncomputable def slotV (j : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 22), Nat.sub j (nat_lit 13),
    nIf(Nat.blt j (nat_lit 27), nIf(Nat.beq j (nat_lit 23), nat_lit 9, Nat.sub j (nat_lit 20)),
      nIf(Nat.blt j (nat_lit 29), Nat.sub j (nat_lit 17), Nat.sub j (nat_lit 63))))

@[expose] noncomputable def NVr (s l : Nat) : Nat := NV (nthN netL s) (Nat.sub (nat_lit 36) l)

@[expose] noncomputable def ptRecS (s x : Nat) : Nat :=
  fld(PTVj s (Nat.shiftRight x (nat_lit 9)), Nat.mul (Nat.land x (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def ptRecV (j x : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 13), CFSG.KD.Fi24Net.ptRec j x, ptRecS (slotV j) x)

@[expose] noncomputable def ptFT (j x : Nat) : Nat :=
  nIf(andB (Nat.blt x (nat_lit 306936)) (net j), Nat.land (ptRecV j x) (nat_lit 524287),
    ptF (NV j) x)

@[expose] noncomputable def ptRT (j x : Nat) : Nat :=
  nIf(andB (Nat.blt x (nat_lit 306936)) (net j),
    Nat.land (Nat.shiftRight (ptRecV j x) (nat_lit 19)) (nat_lit 524287), ptR (NV j) x)

@[expose] noncomputable def tckFV (g : Nat) : Bool :=
  (fun s => CFSG.KC.Fi24Net.genOK (PTVj s) (NV (nthN netL s)) (nat_lit 0) (Nat.mod g (nat_lit 19)))
    (Nat.div g (nat_lit 19))

@[expose] noncomputable def tckRV (g : Nat) : Bool :=
  (fun s => CFSG.KC.Fi24Net.genOK (PTVj s) (NVr s) (nat_lit 19) (Nat.mod g (nat_lit 19)))
    (Nat.div g (nat_lit 19))

end CFSG.KD.Fi24PairK

namespace CFSG.KD.Fi24PairPc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24PairK CFSG.KC.Fi24PairPc
open CFSG.KC.Fi24Net (lidx)
open CFSG.KD.Fi24PairK (NV net ptFT ptRT)

@[expose] noncomputable def ptZV (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), ptRT (lidx m) x, ptFT (lidx m) x))
    (fun n => nIf(Nat.beq n (nat_lit 0), ptFT (nat_lit 0) x, ptRT (lidx (Nat.succ n)) x)) z

@[expose] noncomputable def apZV (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => ptZV z y)) w x

@[expose] noncomputable def eqZV (u v : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (apZV u b) (apZV v b), ih)) cbZ

@[expose] noncomputable def cjOneV (xs : List (List Nat)) (n j k : Nat) (c : List Nat) : Bool :=
  andB (inR (Nat.succ j) n c) (eqZV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c))

@[expose] noncomputable def relHdV (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n j : Nat) : Bool :=
  andB (andB (dirOK net (xW xs j)) (Nat.blt (nat_lit 0) (nthN ps j)))
    (andB (andB (inR (Nat.succ j) n (nthLL pw j))
        (eqZV (pcW xs (rep j (nthN ps j))) (pcW xs (nthLL pw j))))
      (Nat.beq (lenA (nthL3 cj j)) (Nat.sub n (Nat.succ j))))

@[expose] noncomputable def pcCkV (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n g : Nat) : Bool :=
  (fun j k => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (relHdV net xs ps pw cj n j) (Nat.beq j k))
      (cjOneV xs n j k (nthLL (nthL3 cj j) (Nat.sub k (Nat.succ j)))) (Nat.blt j k))
    (Nat.div g n) (Nat.mod g n)

@[expose] noncomputable def genOKV (net : Nat → Bool) (xs : List (List Nat)) (n l : Nat)
    (r : List Nat) : Bool :=
  andB (andB (net l) (inR (nat_lit 0) n r))
    (eqZV [Int.ofNat (Nat.add l (nat_lit 3))] (pcW xs r))

@[expose] noncomputable def cTV (g : Nat) : Bool := pcCkV net J.xsT J.psT J.pwT J.cjT 21 g

@[expose] noncomputable def cAV (g : Nat) : Bool := pcCkV net J.xsA J.psA J.pwA J.cjA 24 g

@[expose] noncomputable def cBV (g : Nat) : Bool := pcCkV net J.xsB J.psB J.pwB J.cjB 23 g

@[expose] noncomputable def gTV (g : Nat) : Bool := genOKV net J.xsT 21 (nthN lvT g) (nthLL J.gwT g)

@[expose] noncomputable def gAV (g : Nat) : Bool := genOKV net J.xsA 24 (nthN lvA g) (nthLL J.gwA g)

@[expose] noncomputable def gBV (g : Nat) : Bool := genOKV net J.xsB 23 (nthN lvB g) (nthLL J.gwB g)

@[expose] noncomputable def gckV (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (gBV (Nat.sub g 22)) (gAV (Nat.sub g 10)) (Nat.blt g 22))
    (gTV g) (Nat.blt g 10)

end CFSG.KD.Fi24PairPc

end
