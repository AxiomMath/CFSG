module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24Pair

#kc_repo #kc_ktree CFSG.KD.Fi24Pair NT "Certificates/Kernel/Sporadic/Fi24Pair/data/nets.bin" 11776 4 211968 3454090310036564770
#kc_repo #kc_ktree CFSG.KD.Fi24Pair HT "Certificates/Kernel/Sporadic/Fi24Pair/data/hnets.bin" 11776 1 23552 16289786244010157421
#kc_repo #kc_ktree CFSG.KD.Fi24Pair XT "Certificates/Kernel/Sporadic/Fi24Pair/data/rows.bin" 2097152 1 2097152 17595220297919311692
#kc_repo #kc_ktree CFSG.KD.Fi24Pair PT "Certificates/Kernel/Sporadic/Fi24Pair/data/fpts.bin" 16384 1 16384 3740549485190918064

public section

namespace CFSG.KD.Fi24Pair

open CFSG.KC.Fi24Pair CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def M : Nat := XT (nat_lit 0)

@[expose] noncomputable def FP (p : Nat) : Nat :=
  fld(PT (nat_lit 0), Nat.mul (nat_lit 32) p, nat_lit 4294967295)

@[expose] noncomputable def r0 : Nat := nat_lit 2678

@[expose] noncomputable def r1 : Nat := nat_lit 652

@[expose] noncomputable def NL : List Nat := (List.range 18).map NT

@[expose] noncomputable def hW0 : List Nat := [2, 9, 5, 11, 14, 1, 11, 1]

@[expose] noncomputable def hW1 : List Nat := [1, 15, 3, 16, 2, 16, 9]

@[expose] noncomputable def wNets (w : List Nat) : List Nat := (w.map NT).reverse

@[expose] noncomputable def clo (k : Nat) : Bool := closedOK (NT k) M

@[expose] noncomputable def LRn (r x : Nat) : Nat :=
  CFSG.KC.Fi24NetPt.letN CFSG.KD.Fi24Net.NW (Nat.add r (nat_lit 4)) x

@[expose] noncomputable def sig (k : Nat) : Bool :=
  sigOK LRn FP (NT k) (Nat.add (nat_lit 4) k)

@[expose] noncomputable def pts : Bool := fOK FP

@[expose] noncomputable def reg : Bool := regionOK M r0 r1

@[expose] noncomputable def orb0 : Bool :=
  Nat.beq (reachK (nat_lit 12) NL r0 (nat_lit 8)) (CFSG.KC.MonsterConv.Perm.ones (nat_lit 3240))

@[expose] noncomputable def hw0 : Bool := hOK (wNets hW0) (HT 0) r0

@[expose] noncomputable def hw1 : Bool := hOK (wNets hW1) (HT 1) r0

@[expose] noncomputable def orb1 : Bool :=
  Nat.beq (CFSG.KC.YModel.popc (nat_lit 12) (Nat.land (reachK (nat_lit 12) [HT 0, HT 1] r1 (nat_lit 64))
    (CFSG.KC.MonsterConv.Perm.ones (nat_lit 3240)))) (nat_lit 1080)

@[expose] noncomputable def outP : Nat → Nat × Nat × Nat × Nat
  | 0 => (124040, 1291, 109856, 1155)
  | 1 => (109856, 1155, 297417, 3135)
  | 2 => (297417, 3135, 124040, 1291)
  | 3 => (0, 3240, 305530, 3240)
  | 4 => (305530, 3240, 73618, 3240)
  | _ => (73618, 3240, 0, 3240)

@[expose] noncomputable def out (j : Nat) : Bool :=
  outOK FP M (outP j).1 (outP j).2.1 (outP j).2.2.1 (outP j).2.2.2

end CFSG.KD.Fi24Pair

end
