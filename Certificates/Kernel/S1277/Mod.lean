module

public import Certificates.Data.Kernel.S1277KMod
public import Certificates.Data.S1277Struct
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.ModData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Mod

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct CFSG.KC.S1277Gm CFSG.KC.S1277Mod
  CFSG.KD.S1277Gm CFSG.KD.S1277Mod

theorem stabg_ok : eqB6 (stabL (gm6P.map B6.ofP) 5) lg = true := by quickRfl

theorem stabn_ok :
    eqB6 (stabL (gm6P.map B6.ofP ++ (gm6P.map B6.ofP).map (·.comp sig6)) 5) ln = true := by
  quickRfl

theorem modg_ok : modChk lg apg cpg ipg oneg = true := by quickRfl

theorem modn_ok : modChk ln apn cpn ipn onen = true := by quickRfl

end CFSG.KP.S1277Mod

end
