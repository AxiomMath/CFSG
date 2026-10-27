module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Data.Kernel.Spor.WordProg
public import CFSG.Certificates.Kernel.Orders.CertSplit
public import CFSG.Certificates.Kernel.Orders.Mat3

public section

namespace CFSG.KD.Fi23M

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 64009) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 253) 1

@[expose] noncomputable def CI : Nat := CFSG.KC.Ord.rep1 253 253

@[expose] noncomputable def ONE : Nat := CFSG.KC.Ord.rep1 254 253

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 253 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 253) i)))) 253

@[expose] noncomputable def MUL : Nat → Nat → Nat := CFSG.KC.Ord.mul3s 253 64009 LO CI RM

@[expose] noncomputable def VLD : Nat → Bool := CFSG.KC.Ord.valid3 64009 LO

end CFSG.KD.Fi23M

#kc_repo #kc_ktree CFSG.KD.Fi23M MT "Certificates/Kernel/Fi23M/data/mats.bin" 16003 4 208039 18280033295982358323
#kc_repo #kc_json_family_gz CFSG.KD.Fi23M "Certificates/Kernel/Fi23M/data/lists.json.gz" 2092 6363451889728345144
  (PS : List Nat) (WC : List Nat) (PR : List Nat)

public section

namespace CFSG.KD.Fi23M

@[expose] noncomputable def RB (k : Nat) : Nat :=
  [nat_lit 0, MT 0, MT 1, MT 0, MT 2].getD k (nat_lit 0)

@[expose] noncomputable def RS (k : Nat) : Nat :=
  [MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 11, MT 12].getD k (nat_lit 0)

end CFSG.KD.Fi23M

end

#kc_listDispatch CFSG.KD.Fi23M PS PS 10
#kc_listDispatch CFSG.KD.Fi23M WC WC 10
#kc_listDispatch CFSG.KD.Fi23M PR PR 5
