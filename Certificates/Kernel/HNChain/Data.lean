module

public import Certificates.Data.Kernel.HNLocalK
public import Certificates.Data.Kernel.HNMultK
public import Certificates.Kernel.HNLocal.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CFSG.KD.HNChain.RB "Certificates/Kernel/HNChain/data/rb.bin" 1034105 1507436749272669732
#kc_repo #kc_items_root CFSG.KD.HNChain.GT "Certificates/Kernel/HNChain/data/g.bin" 229980 3685617682762725942
#kc_repo #kc_items_root CFSG.KD.HNChain.VT "Certificates/Kernel/HNChain/data/v.bin" 215 9307419170724955277
#kc_repo #kc_items_root CFSG.KD.HNChain.XS "Certificates/Kernel/HNChain/data/xs.bin" 1690 16969162413094916911
#kc_repo #kc_items_root CFSG.KD.HNChain.PINS "Certificates/Kernel/HNChain/data/pin.bin" 268 11278931764514950169
#kc_repo #kc_items_root CFSG.KD.HNChain.WDN "Certificates/Kernel/HNChain/data/wd.bin" 252 4884478918817554309
#kc_repo #kc_items_root CFSG.KD.HNChain.P3 "Certificates/Kernel/HNChain/data/par3.bin" 154 1876215793329425467
#kc_repo #kc_ktree CFSG.KD.HNChain XC1 "Certificates/Kernel/HNChain/data/x1.bin" 6650 4 525350 3165297146958635589
#kc_repo #kc_ktree CFSG.KD.HNChain TD1 "Certificates/Kernel/HNChain/data/t1.bin" 217 4 17360 16258999763042424999
#kc_repo #kc_ktree CFSG.KD.HNChain SD1 "Certificates/Kernel/HNChain/data/s1.bin" 350 4 28000 14041110103821835033
#kc_repo #kc_ktree CFSG.KD.HNChain XC2 "Certificates/Kernel/HNChain/data/x2.bin" 6650 4 39900 10886475637868037348
#kc_repo #kc_ktree CFSG.KD.HNChain TD2 "Certificates/Kernel/HNChain/data/t2.bin" 270 4 1890 14536912541478171777
#kc_repo #kc_ktree CFSG.KD.HNChain SD2 "Certificates/Kernel/HNChain/data/s2.bin" 350 4 2450 13426502945041371490

public section

namespace CFSG.KD.HNChain

@[expose] noncomputable def G10 : Nat := GT 0
@[expose] noncomputable def G11 : Nat := GT 1

@[expose] noncomputable def G20 : Nat := GT 2
@[expose] noncomputable def G21 : Nat := GT 3

@[expose] noncomputable def G30 : Nat := GT 4
@[expose] noncomputable def G31 : Nat := GT 5
@[expose] noncomputable def G32 : Nat := GT 6
@[expose] noncomputable def G33 : Nat := GT 7

@[expose] noncomputable def V0 : Nat := VT 0
@[expose] noncomputable def V1 : Nat := VT 1
@[expose] noncomputable def V2 : Nat := VT 2
@[expose] noncomputable def V3 : Nat := VT 3

@[expose] noncomputable def X3 : Nat := XS 0
@[expose] noncomputable def S3 : Nat := XS 1

@[expose] noncomputable def XC3 (_ : Nat) : Nat := X3

@[expose] noncomputable def SD3 (_ : Nat) : Nat := S3

@[expose] noncomputable def PI (s k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (PINS s) (Nat.mul 16 k)) 65535

@[expose] def wordOf : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => bif Nat.beq n 0 then [] else (n % 256 - 1) :: wordOf f (n / 256)

@[expose] noncomputable def WDL (k : Nat) : List Nat := wordOf 64 (WDN k)

@[expose] noncomputable def PAR3 : List Nat := (List.range 31).map P3

end CFSG.KD.HNChain

end
