module

public import Certificates.Data.Kernel.F4Syl3Cls
public import Certificates.Kernel.F4Syl3.ModelChk
public import Certificates.Kernel.F4Syl3.RelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Syl3 "Certificates/Kernel/F4Syl3/data/cls.json.gz" 9719
  6910850899827987092 (cpar : List Nat) (clet : List Nat) (ca : List Nat) (cb : List Nat)
  (cdep : List Nat) (cw : List Nat) (cl : List Nat) (pS : List Nat)

#kc_each CFSG.KD.F4Syl3.ch799602cls r (fun k => CFSG.KC.F4Syl3.clsRowN CFSG.KD.F4Syl3.pS
  CFSG.KD.F4Syl3.tgt CFSG.KD.F4Syl3.cpar CFSG.KD.F4Syl3.clet CFSG.KD.F4Syl3.ca CFSG.KD.F4Syl3.cb
  CFSG.KD.F4Syl3.cw CFSG.KD.F4Syl3.cl k == 1) 0 48

namespace CFSG.KD.F4Syl3

open CFSG.KC.F4Syl3

theorem pin_ok : pinB pS w4 l4 w5 l5 = true := by decide +kernel

theorem cls_model_ok : clsModelB tgt cover cpar ca cb cdep = true := by decide +kernel

theorem cls_neg_tgt : clsRowN pS (tgt.map fun t => (t + 1) % 3) cpar clet ca cb cw cl 1 = 0 := by
  decide +kernel

theorem cls_neg_let : clsRowN pS tgt cpar (clet.map fun c => (c + 1) % 8) ca cb cw cl
    (cpar.findIdx (· != 48)) = 0 := by
  decide +kernel

end CFSG.KD.F4Syl3

end
