module

public import Certificates.Data.Kernel.S1277K7214
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.C7214Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KD.S1277Gm
  CFSG.KD.C7214

theorem ok1 : chk1 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok2 : chk2 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok3 : chk3 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok4 : eqB6 ((gm6P.map B6.ofP).filter fun g => Nat.beq (appK g 1) 1) st1P = true := by
  quickRfl

theorem ok5 : chk5 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok6 : chk6 (st1P.map B6.ofP) = true := by quickRfl

theorem ok7 : chk7 (st1P.map B6.ofP) = true := by quickRfl

theorem ok8 : chk8 (st1P.map B6.ofP) = true := by quickRfl

theorem ok9 : chk9 (st1P.map B6.ofP) = true := by quickRfl

theorem ok10 : chk10 (st1P.map B6.ofP) w10 = true := by quickRfl

theorem ok14 : chk14 (gm6P.map B6.ofP) = true := by quickRfl

end CFSG.KP.C7214

end
