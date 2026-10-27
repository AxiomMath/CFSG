module

public import Certificates.Data.Kernel.F4InvComm
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Inv "Certificates/Kernel/F4Inv/data/long.json.gz" 103
  14727494982522844257 (lw : List Nat) (ll : List Nat)

#kc_each CFSG.KD.F4Inv.ch799601long r (fun k => CFSG.KC.F4Inv.longN (CFSG.KD.F4Inv.lw.getD k 0)
  (CFSG.KD.F4Inv.ll.getD k 0) (CFSG.KC.F4Inv.longPos.getD k 0) == 1) 0 12

namespace CFSG.KD.F4Inv

open CFSG.KC.F4Inv

theorem long_neg : longN (lw.getD 1 0) (ll.getD 1 0) (longPos.getD 0 0) = 0 := by decide +kernel

theorem long_neg_len : longN (lw.getD 0 0) 6 (longPos.getD 0 0) = 0 := by decide +kernel

end CFSG.KD.F4Inv

end
