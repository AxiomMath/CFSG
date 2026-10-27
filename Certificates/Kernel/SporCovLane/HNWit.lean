module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.ChainKit
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Kernel.SporCovLane.HNWitWords
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel

set_option Elab.async false

public section

namespace CFSG.KD.SporCovLane.HNWit

open CFSG.KC.SporCov CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

@[expose] noncomputable def neq (mw : List Nat → Nat) (j : Nat) : Bool :=
  !eqM mw [U, C] (C :: repW [U] (j + 1))

@[expose] noncomputable def chk (mw : List Nat → Nat) : Bool :=
  eqM mw (repW [U] 5) [] && !eqM mw [U] [] && neq mw 0 && neq mw 1 && neq mw 2 && neq mw 3

@[expose] noncomputable def kit (k : (List Nat → Nat) → Bool) : Bool :=
  kitC mul CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) (mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)) Ws k

namespace Ck

theorem ok : kit chk = true := by
  quickRfl

end Ck

end CFSG.KD.SporCovLane.HNWit

end
