module

public import Certificates.Data.Kernel.Hall82K.Enum
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Hall82E "Certificates/Kernel/Hall82K/data/hall82enum.items.gz" 42148 8187696255565631042
  ME MPA MSG MCT LE LPA LSG LCT

public section

namespace CFSG.KD.Hall82E

open CFSG.KC.Hall82K

@[expose] noncomputable def EM (k : Nat) : Nat := lane ME 36 68719476735 k
@[expose] noncomputable def PM (k : Nat) : Nat := lane MPA 32 4294967295 k
@[expose] noncomputable def SM (k : Nat) : Nat := lane MSG 12 4095 k
@[expose] noncomputable def CM (k : Nat) : Nat := lane MCT 12 4095 k
@[expose] noncomputable def EL (k : Nat) : Nat := lane LE 36 68719476735 k
@[expose] noncomputable def PL (k : Nat) : Nat := lane LPA 32 4294967295 k
@[expose] noncomputable def SL (k : Nat) : Nat := lane LSG 12 4095 k
@[expose] noncomputable def CL (k : Nat) : Nat := lane LCT 12 4095 k

@[expose] def hallLGensK : List Nat := [52077576321, 61871938592]

@[expose] noncomputable def enumMAt (k : Nat) : Bool :=
  enumAt 4439643498 34633937090 2160 EM PM SM CM k

@[expose] noncomputable def enumLAt (k : Nat) : Bool :=
  enumAt 52077576321 61871938592 1080 EL PL SL CL k

end CFSG.KD.Hall82E
