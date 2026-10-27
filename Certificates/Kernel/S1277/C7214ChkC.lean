module

public import Certificates.Data.Kernel.S1277K7214
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.C7214Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KD.S1277Gm
  CFSG.KD.C7214

theorem ok16 : chk16 ((gm6P.map sigP).map B6.ofP) ((gm6P ++ gm6P.map sigP).map B6.ofP) yb = true := by
  quickRfl

theorem ok17 : chk17 ((gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok18 : chk18 ((gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok19 : chk19 ((gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok24 : chk24 ((gm6P.map sigP).map B6.ofP) ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by
  quickRfl

end CFSG.KP.C7214

end
