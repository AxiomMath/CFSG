module

public import Certificates.Data.Kernel.F4Syl3PhiInv
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Syl3 "Certificates/Kernel/F4Syl3/data/phi.json.gz" 858
  16350917158555814213 (wa : Nat) (la : Nat) (waf : Nat) (wb : Nat) (lb : Nat)

#kc_repo #kc_json_gz CFSG.KD.F4Syl3 "Certificates/Kernel/F4Syl3/data/inv.json.gz" 5083
  7431744092612327882 (iw : List Nat) (il : List Nat) (iwr : List Nat)

#kc_each CFSG.KD.F4Syl3.ch799602inv r (fun k => CFSG.KC.F4Syl3.invN k (CFSG.KD.F4Syl3.iw.getD k 0)
  (CFSG.KD.F4Syl3.il.getD k 0) (CFSG.KD.F4Syl3.iwr.getD k 0) == 1) 0 8

namespace CFSG.KD.F4Syl3

open CFSG.KC.F4Syl3

theorem phi_ok : phiN wa la waf wb lb = 1 := by decide +kernel

theorem phi_neg : phiN wa la wa wb lb = 0 := by decide +kernel

theorem inv_neg : invN 0 wb lb wb = 0 := by decide +kernel

theorem inv_neg_rho : invN 1 (iw.getD 0 0) (il.getD 0 0) (iwr.getD 0 0) = 0 := by decide +kernel

end CFSG.KD.F4Syl3

end
