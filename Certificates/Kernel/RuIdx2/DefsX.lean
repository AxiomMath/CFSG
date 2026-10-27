module

public import Certificates.Kernel.RuIdx2.Defs
public import Certificates.Data.Kernel.RuIdx2.DataX
public import Certificates.Data.Kernel.RuIdx2XK
public import Certificates.Data.Kernel.RuDc.Defs

public section

namespace CFSG.KD.RuIdx2

open CFSG.KC.SLDc CFSG.KC.RuIdx2

@[expose] noncomputable def QU (k : Nat) : List Nat := List.getD [QU0, QU1, QU2, QU3, QU4, QU5, QU6] k []

@[expose] noncomputable def tgtU (i : Nat) : List Nat :=
  (fun p => conjW QCI QC (unW (XW (Nat.shiftRight p (nat_lit 1)))) (tau 2) (IL (tau 2)) (QS.getD i 0)
    (Nat.land p (nat_lit 1))) ((ex 2).getD i 0)

@[expose] noncomputable def tgt (k : Nat) : List Nat :=
  bif Nat.beq k (nat_lit 0) then QCI ++ QC else
    bif Nat.blt k (nat_lit 5) then QCI ++ (unW (RG 2 (Nat.sub k (nat_lit 1))) ++ QC) else
      tgtU (Nat.sub k (nat_lit 5))

@[expose] noncomputable def famX (k : Nat) : Bool :=
  QS.all (fun s => Nat.blt s (nat_lit 2)) && vaK CFSG.KD.RuDc.C (eMem CFSG.KD.RuDc.C CFSG.KD.RuDc.D 1) (QU k) (tgt k)

@[expose] noncomputable def famT : Bool :=
  ((CFSG.KD.RuDc.D.Rc.flatten.filter fun r : Rep => Rep.cls r == 5).map Rep.w) ==
    (List.range 839).map fun j => unW (XW j)

end CFSG.KD.RuIdx2

end
