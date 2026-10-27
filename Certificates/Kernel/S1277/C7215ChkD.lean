module

public import Certificates.Data.Kernel.S1277K7215
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.C7215Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KC.C7215
  CFSG.KD.S1277Gm CFSG.KD.C7215

theorem ok1 : ck1 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok10 : ck10 gmIdx w10 = true := by quickRfl

theorem ok15 : ckO fixP1K (gm6P.map B6.ofP) l1 = true := by quickRfl

theorem ok18 : ckO onQuotK (gm6P.map B6.ofP) l2 = true := by quickRfl

theorem ok23 : ck23 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok24 : ck24 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok25 : ck25 ((gm6P ++ gm6P.map sigP).map B6.ofP) = true := by quickRfl

end CFSG.KP.C7215

end
