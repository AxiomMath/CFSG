module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.Kernel.Spor.PChain
public import Certificates.Data.Kernel.F3Bfs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23K.Eqs
public import Certificates.Kernel.Fi23K.Trees

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum

@[expose] noncomputable def eqS (k0 nk lo c : Nat) : Bool := eqSl G EL ER k0 nk lo c

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  eqS (nat_lit 0) (nat_lit 65) (Nat.mul s (nat_lit 2048)) (nat_lit 2048)
@[expose] noncomputable def surjSl (s : Nat) : Bool :=
  eqS (nat_lit 65) (nat_lit 31) (Nat.mul s (nat_lit 1024)) (nat_lit 1024)
@[expose] noncomputable def chainSl (s : Nat) : Bool :=
  eqS (nat_lit 96) (nat_lit 40) (Nat.mul s (nat_lit 1024)) (nat_lit 1024)
@[expose] noncomputable def miscSl (s : Nat) : Bool :=
  eqS (nat_lit 136) (nat_lit 14) (Nat.mul s (nat_lit 4096)) (nat_lit 4096)

@[expose] noncomputable def LL (l x : Nat) : Nat := tb G (Nat.add (nat_lit 52) l) x

@[expose] noncomputable def BB (i : Nat) : Nat := i

@[expose] noncomputable def lvOf (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 6), nat_lit 1, i)

@[expose] noncomputable def rootOf (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 6), nat_lit 2, i)

@[expose] noncomputable def treeK (i lo len : Nat) : Bool :=
  tbfsSlK (nat_lit 31671) (CNT i) (lvK LL BB (nat_lit 24) (lvOf i)).length LL
    (lvAt LL BB (nat_lit 24) (lvOf i)) (TT i (nat_lit 0)) (TT i (nat_lit 1)) (TT i (nat_lit 2))
    (TT i (nat_lit 3)) (TT i (nat_lit 4)) lo len

@[expose] noncomputable def treeSl (i c : Nat) : Bool :=
  treeK i (Nat.mul c (nat_lit 2048)) (nat_lit 2048)

@[expose] noncomputable def hdAt (i : Nat) : Bool :=
  tbfsHdK (nat_lit 31671) (rootOf i) (CNT i) (TT i (nat_lit 0)) (TT i (nat_lit 1))
    (TT i (nat_lit 2)) (TT i (nat_lit 3))

@[expose] noncomputable def t0Sl (c : Nat) : Bool := treeSl (nat_lit 0) c
@[expose] noncomputable def t2Sl (c : Nat) : Bool := treeSl (nat_lit 2) c
@[expose] noncomputable def t6Sl (c : Nat) : Bool := treeSl (nat_lit 6) c
@[expose] noncomputable def tSmall : Bool :=
  bAnd(treeSl (nat_lit 1) (nat_lit 0), bAnd(treeSl (nat_lit 1) (nat_lit 1),
    bAnd(treeSl (nat_lit 3) (nat_lit 0), bAnd(treeSl (nat_lit 4) (nat_lit 0),
      treeSl (nat_lit 5) (nat_lit 0)))))

@[expose] noncomputable def bfsK : Bool :=
  CFSG.KC.F3Bfs.bfsOrderOK (tb G (nat_lit 39)) (tb G (nat_lit 40)) (tb G (nat_lit 91))
    (tb G (nat_lit 92)) (nat_lit 31671)

@[expose] noncomputable def depK : Bool :=
  bAnd(Nat.beq (tb G (nat_lit 93) (nat_lit 0)) (nat_lit 0),
    allN (nat_lit 31671) fun k => strictB (tb G (nat_lit 93) k) fun e => bAnd(Nat.blt e (nat_lit 200),
      bIf(Nat.beq k (nat_lit 0), true,
        Nat.beq e (Nat.succ (tb G (nat_lit 93) (tb G (nat_lit 91) k))))))

@[expose] noncomputable def coverK : Bool :=
  allN (nat_lit 31671) fun p => bIf(Nat.beq p (nat_lit 0), true,
    bIf(bAnd(Nat.blt (r32 (TT (nat_lit 1) (nat_lit 1)) p) (CNT (nat_lit 1)),
        Nat.beq (r32 (TT (nat_lit 1) (nat_lit 0)) (r32 (TT (nat_lit 1) (nat_lit 1)) p)) p), true,
      bAnd(Nat.blt (r32 (TT (nat_lit 6) (nat_lit 1)) p) (CNT (nat_lit 6)),
        Nat.beq (r32 (TT (nat_lit 6) (nat_lit 0)) (r32 (TT (nat_lit 6) (nat_lit 1)) p)) p)))

@[expose] noncomputable def siftChk : Bool :=
  siftK LL (fun i => TT i (nat_lit 1)) (fun i => TT i (nat_lit 2)) (fun i => TT i (nat_lit 3)) CNT
    BB [0, 1, 2, 3, 4, 5] (nat_lit 6) (nat_lit 0) (mapK (tb G (nat_lit 40)) [0, 1, 2, 3, 4, 5])

@[expose] noncomputable def moveK : Bool :=
  bAnd(Bool.not (Nat.beq (LL (nat_lit 2) (nat_lit 0)) (nat_lit 0)),
    Bool.not (Nat.beq (tb G (nat_lit 39) (LL (nat_lit 2) (nat_lit 0))) (nat_lit 0)))

end CFSG.KD.Fi23K

end
