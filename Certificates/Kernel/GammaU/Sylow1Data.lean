module

public import Certificates.Data.Kernel.GammaUSylowK
public import Certificates.Data.Kernel.IdxFourSiftK
public import Certificates.Kernel.GammaU.Sigma1Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUY1 "Certificates/Kernel/GammaU/data/syl1.json.gz" 52025
  1184371445786422178 (AB : List Nat) (AO : List Nat) (ASP : Nat) (ASI : Nat)
  (AWD : List (List Nat)) (ATL : List (List Nat)) (AT : List Nat) (APS : List Nat)
  (ATR : List (List (List Nat))) (AR : List (List (List Nat))) (Y : Nat) (QS : List (List Nat))
  (ZP : Nat) (DP : Nat) (E : List (List Nat))

namespace CFSG.KD.GUY1

open CFSG.KC.IF4C

@[expose] noncomputable def TS : List Nat := [look ASP 0, look ASP 1, Y]

@[expose] noncomputable def blk (i c : Nat) : Bool := blkOK ASP AT AO ATL AR i c

@[expose] noncomputable def lvl (i : Nat) : Bool :=
  cntOK AO ATL AR i && treeOK ASP AT AO ATL ATR i && posOK AT AO APS AB i

@[expose] noncomputable def gens : Bool :=
  tlOK ASP AB ATL 3 1 && invOK ASP ASI 3 && wordsOK ASP ASI 3 AWD 2

end CFSG.KD.GUY1

end
