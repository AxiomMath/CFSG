module

public import Certificates.Data.Kernel.S1277K7214
public import Certificates.Kernel.S1277.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KD.S1277Gm

theorem ok11 : chk11 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok12 : chk12 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok13 : chk13 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok15 : chk15 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok25 : chk25 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

theorem ok26 : chk26 (gm6P.map B6.ofP) ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

end CFSG.KP.C7214

end
