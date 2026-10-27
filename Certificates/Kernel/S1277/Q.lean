module

public import Certificates.Data.Kernel.S1277KQ
public import Certificates.Kernel.S1277.Data
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zz
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.S1277Q

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KD.S1277Gm CFSG.KC.S1277ML CFSG.KC.S1277Q

@[expose] def T6 : ℕ := 2353925152621495867340173602361637340156354640058374950912

theorem t6_ok : allBelow (fun v => Nat.beq (fld T6 3 v) (oPts.idxOf (pn v) % 6)) 64 = true := by
  quickRfl

theorem q_ok : qChk T6 (gm6P ++ gm6P.map sigP) = true := by quickRfl

end CFSG.KP.S1277Q

end
