module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Data.Kernel.Spor.WordProg
public import CFSG.Certificates.Kernel.Orders.CertSplit
public import CFSG.Certificates.Kernel.Orders.Mat3

public section

namespace CFSG.KD.BrFi24

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 609961) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 781) 1

@[expose] noncomputable def CI : Nat := CFSG.KC.Ord.rep1 781 781

@[expose] noncomputable def ONE : Nat := CFSG.KC.Ord.rep1 782 781

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 781 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 781) i)))) 781

@[expose] noncomputable def MUL : Nat → Nat → Nat := CFSG.KC.Ord.mul3s 781 609961 LO CI RM

@[expose] noncomputable def VLD : Nat → Bool := CFSG.KC.Ord.valid3 609961 LO

end CFSG.KD.BrFi24

#kc_repo #kc_ktree CFSG.KD.BrFi24 MT "Certificates/Kernel/Sporadic/Fi24Br/data/mats.bin" 152491 5 3964766 4025252237917697900
#kc_repo #kc_json_family_gz CFSG.KD.BrFi24 "Certificates/Kernel/Sporadic/Fi24Br/data/lists.json.gz" 2898 4682609518542707417
  (PS : List Nat) (WC : List Nat) (PR : List Nat)
#kc_repo #kc_json_gz CFSG.KD.BrFi24 "Certificates/Kernel/Sporadic/Fi24Br/data/lists.json.gz" 2898 4682609518542707417
  (CVL : List Nat)

public section

namespace CFSG.KD.BrFi24

@[expose] noncomputable def RB (k : Nat) : Nat :=
  [nat_lit 0, MT 0, MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 11,
    MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 12, MT 10, MT 13, MT 25].getD k (nat_lit 0)

@[expose] noncomputable def RS (k : Nat) : Nat :=
  [MT 13, MT 14, MT 15, MT 16, MT 17, MT 18, MT 19, MT 20, MT 21, MT 22, MT 23, MT 24,
    MT 25].getD k (nat_lit 0)

end CFSG.KD.BrFi24

end

#kc_listDispatch CFSG.KD.BrFi24 PS PS 13
#kc_listDispatch CFSG.KD.BrFi24 WC WC 13
#kc_listDispatch CFSG.KD.BrFi24 PR PR 70
#kc_repo #kc_ktree CFSG.KD.BrFi24 P1 "CFSG/Blueprint/Data/F24G1-f3r781B0.m1" 256 4 617792 11363172329627773443
#kc_repo #kc_ktree CFSG.KD.BrFi24 P2 "CFSG/Blueprint/Data/F24G1-f3r781B0.m2" 256 4 617792 12512628901586912669
