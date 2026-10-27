module

public import Certificates.Data.Kernel.SuzDc2.Defs

public section

namespace CFSG.KD.SuzDc2

open CFSG.KC.SLDc

@[expose] noncomputable def actS (l : Nat) (x : List Nat) : List Nat :=
  x.map fun p => bif Nat.blt p 22880 then L l p else 0

@[expose] noncomputable def rowF (l : Nat) (e : Nat × List Nat) : Bool :=
  Nat.blt e.1 SB.C.flatten.length && lookC SB.B SB.C e.1 == actS l e.2

@[expose] noncomputable def rowS (l j : Nat) : Bool :=
  (((List.zip (SB.rows.getD l []) SB.C.flatten).drop (820 * j)).take 820).all (rowF l)

@[expose] noncomputable def treeF (i : Nat) (e : (Nat × Nat) × List Nat) : Bool :=
  Nat.beq i 0 || (Nat.blt e.1.1 i && Nat.blt e.1.2 5 && actS e.1.2 (lookC SB.B SB.C e.1.1) == e.2)

@[expose] noncomputable def treeS (j : Nat) : Bool :=
  allIdx treeF (0 + 820 * j)
    (((List.zip (List.zip SB.par SB.via) SB.C.flatten).drop (820 * j)).take 820)

@[expose] noncomputable def sortS (j : Nat) : Bool :=
  sortedLt (((SB.ord.map (lookC SB.B SB.C)).drop (820 * j)).take (820 + 1))

end CFSG.KD.SuzDc2

end
