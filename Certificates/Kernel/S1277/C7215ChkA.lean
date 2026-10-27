module

public import Certificates.Data.Kernel.S1277K7215
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.C7215Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KC.C7215
  CFSG.KD.S1277Gm CFSG.KD.C7215

theorem okP : eqB6 ((gm6P.map B6.ofP).filter (presvK p1c)) p1P = true := by quickRfl

theorem okQ : eqB6 ((gm6P.map B6.ofP).filter (presvK l2c)) l2P = true := by quickRfl

theorem ok2 : ckN (p1P.map B6.ofP) r1 = true := by quickRfl

theorem ok3 : ckT (p1P.map B6.ofP) r1 = true := by quickRfl

theorem ok4 : ckN (l2P.map B6.ofP) r2 = true := by quickRfl

theorem ok5 : ckT (l2P.map B6.ofP) r2 = true := by quickRfl

theorem ok6 : ck6 = true := by quickRfl

theorem ok7 : ck7 = true := by quickRfl

theorem ok8 : ck8 (p1P.map B6.ofP) = true := by quickRfl

theorem ok9 : ck9 (p1P.map B6.ofP) = true := by quickRfl

theorem ok13 : ckY (p1P.map B6.ofP) l1 = true := by quickRfl

theorem ok14 : ckU (p1P.map B6.ofP) l1 = true := by quickRfl

theorem ok16 : ckY (l2P.map B6.ofP) l2 = true := by quickRfl

theorem ok17 : ckU (l2P.map B6.ofP) l2 = true := by quickRfl

theorem ok19 : ckZo (p1P.map B6.ofP) l1 = true := by quickRfl

theorem ok20 : ckZs (p1P.map B6.ofP) l1 = true := by quickRfl

theorem ok21 : ckZo (l2P.map B6.ofP) l2 = true := by quickRfl

theorem ok22 : ckZs (l2P.map B6.ofP) l2 = true := by quickRfl

end CFSG.KP.C7215

end
