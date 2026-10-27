module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
public import Certificates.Data.Kernel.Spor.Fi24FreeK

#kc_repo #kc_json_gz CFSG.KD.Fi24FreeK "Certificates/Kernel/Sporadic/Fi24FreeK/data/freek.json.gz" 858 1451454312685555988 (rl : List (List Nat)) (gh : List Nat) (wq : List Nat) (lw : List (List Nat × List Nat)) (mv : Nat)
#kc_repo #kc_ktree_gz CFSG.KD.Fi24FreeK PPT "Certificates/Kernel/Sporadic/Fi24FreeK/data/pp.bin.gz" 65536 1 65536 264977953379080611

public section

namespace CFSG.KD.Fi24FreeK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24FreeK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO

@[expose] noncomputable def c0 : Nat := nat_lit 254589

@[expose] noncomputable def c1 : Nat := nat_lit 61582

@[expose] noncomputable def wc0 : List Nat := [21, 16, 8, 1]

@[expose] noncomputable def wc1 : List Nat := [20, 13, 1]

@[expose] noncomputable def xQ (p : Nat) : Nat := xP OL NT c0 c1 p

@[expose] noncomputable def lam : List Nat := [0, 305530, 73618, 254589, 61582, 65697]

@[expose] noncomputable def PP : Nat := PPT (nat_lit 0)

@[expose] noncomputable def pts : Bool :=
  andB (Nat.beq (ptC NW NT wc0 0) c0) (Nat.beq (ptC NW NT wc1 0) c1)

@[expose] noncomputable def frm : Bool :=
  andB (Nat.beq (clsK OL NT 0 305530) 73618) (andB (Nat.beq (clsK OL NT c0 c1) 65697)
    (andB (Nat.beq (clsK OL NT 0 c0) c0) (andB (Nat.beq (clsK OL NT 0 c1) c1)
      (andB (Nat.beq (clsK OL NT 305530 c0) c0) (Nat.beq (clsK OL NT 305530 c1) c1)))))

@[expose] noncomputable def cj (b : Nat) : Bool :=
  (fun p => Nat.beq (ptC NW NT (G1 ++ [2]) p) (xQ (ptC NW NT G1 p))) (nthD 0 base b)

@[expose] noncomputable def ef : Bool :=
  allL (fun E => allL (fun p => Nat.beq (ptC NW NT E p) p) [0, 305530, c0, c1]) eps

@[expose] noncomputable def e0m : Bool := notB (Nat.beq (ptC NW NT (nthD [] eps 0) mv) mv)

@[expose] noncomputable def rel (i : Nat) : Bool :=
  (fun w => allL (fun b => Nat.beq (ptC NW NT w b) b) base) (epsL (nthD [] rl i))

@[expose] noncomputable def ghk : Bool :=
  andB (Nat.beq (lenL gh) 12) (allI (fun i y => Nat.beq (ptC NW NT G1 (nthD 0 hr i)) y) gh 0)

@[expose] noncomputable def memB (y : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a y) ih) l

@[expose] noncomputable def stk (i : Nat) : Bool :=
  (fun y => orB (notB (ppB OL NT c0 c1 y)) (andB (Nat.beq (bitN PP y) 1)
      (orB (failB OL NT c0 c1 y (nthD 0 wq i)) (memB y lam))))
    (nthD 0 gh i)

@[expose] noncomputable def ppc : Bool := andB (Nat.beq (Nat.land PP ptsM) PP) (closW NW NT hw PP)

@[expose] noncomputable def lmp : Bool :=
  allL (fun w => allL (fun a => memB (ptC NW NT w a) lam) lam) hw

@[expose] noncomputable def lmk (j : Nat) : Bool :=
  (fun e : List Nat × List Nat => lamOK NW NT OL c0 c1 PP (nthD 0 lam j) e.1 e.2) (nthD ([], []) lw j)

end CFSG.KD.Fi24FreeK

end
