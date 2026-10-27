module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.OrdP
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel

set_option Elab.async false

public section

namespace CFSG.KD.W4RowLane.Ly

open CFSG.KC.SporCov CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 12 1332 111 8 CFSG.KD.FamLySeed.L CFSG.KD.FamLySeed.H CFSG.KD.FamLySeed.CM
    CFSG.KD.FamLySeed.RM

@[expose] def cW : List Nat := [2, 0, 2, 0, 2]

@[expose] def pW : List Nat := cjK cW [0] ++ [0]

@[expose] noncomputable def chk (mw : List Nat → Nat) : Bool :=
  ordPK mul CFSG.KD.FamLySeed.ONE (mw pW) 67

namespace Ck

theorem ok : kitLn mul CFSG.KD.FamLySeed.ONE (CFSG.KD.FamLySeed.RW 1) (CFSG.KD.FamLySeed.RW 1)
    (CFSG.KD.FamLySeed.RW 2) (powR mul CFSG.KD.FamLySeed.ONE (CFSG.KD.FamLySeed.RW 2) 4) [] chk =
      true := by
  quickRfl

end Ck

end CFSG.KD.W4RowLane.Ly

end
