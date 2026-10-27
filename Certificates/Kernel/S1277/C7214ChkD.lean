module

public import Certificates.Data.Kernel.S1277K7214
public import Certificates.Kernel.S1277.Data
public import Certificates.Kernel.S1277.C7214Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KD.S1277Gm
  CFSG.KD.C7214

theorem ok20 : chkCl (prodK l1) (d1P.map B6.ofP) = true := by quickRfl

theorem ok21 : chkCl (prodK l2) (d2P.map B6.ofP) = true := by quickRfl

theorem ok22 : chkZ (prodK l1) (l1 ++ s0pK) i1 = true := by quickRfl

theorem ok23 : chkZ (prodK l2) (l2 ++ s0pK) i2 = true := by quickRfl

theorem ok27 : chk27 = true := by quickRfl

theorem ok28a : chk28 (gm6P.map B6.ofP) = true := by quickRfl

theorem ok28b : chk28 ((gm6P.map sigP).map B6.ofP) = true := by quickRfl

end CFSG.KP.C7214

end
