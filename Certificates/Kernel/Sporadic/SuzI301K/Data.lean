module

public import Certificates.Data.Kernel.LinRep
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json CFSG.KD.SuzI301 "Certificates/Kernel/Sporadic/SuzI301K/data/lin810302.json"
  353557 10124200307978346953
  (QJ : List Nat) (CW : List Nat) (IV : List Nat) (HW : List Nat) (GW : List Nat) (GT : List Nat)
  (N : Nat) (ORD : List Nat) (CX : List Nat)

#kc_repo #kc_ktree CFSG.KD.SuzI301 TB
  "Certificates/Kernel/Sporadic/SuzI301K/data/tb810302.bin" 8192 6 414720 14167582518456104527

#kc_repo #kc_ktree CFSG.KD.SuzI301 RW
  "Certificates/Kernel/Sporadic/SuzI301K/data/rw810302.bin" 32768 6 1658880 3157012183386048855
