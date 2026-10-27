module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.OrdP
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
public import Certificates.Kernel.SporSch.HN.PtC

set_option Elab.async false

public section

namespace CFSG.KD.W4RowLane.HN

open CFSG.KC.SporCov CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

@[expose] def uK : List Nat := [2, 2, 0, 2, 0, 2, 0]

@[expose] def aK₁ : List Nat := [2, 0, 2, 0, 2, 2]

@[expose] def aK₂ : List Nat := [2, 0, 2, 0, 2, 2, 0, 2, 0, 2]

@[expose] def uK₁ : List Nat := [2, 0]

@[expose] def uK₂ : List Nat := [0, 2, 0, 2]

@[expose] def cK : List Nat := [2, 0, 2, 2, 0, 2, 2, 0, 2]

@[expose] noncomputable def cjM (mw : List Nat → Nat) (X : Nat) (g : List Nat) : Nat :=
  mul (mul (mw g) X) (mw (invK g))

@[expose] noncomputable def triM (mw : List Nat → Nat) (X : Nat) (g₁ g₂ : List Nat) : Nat :=
  mul (mul X (cjM mw X g₁)) (cjM mw X g₂)

@[expose] noncomputable def tr5 (X : Nat) : Nat := Nat.mod (trR 13 1729 133 X) 5

@[expose] noncomputable def chk (C : Nat) (mw : List Nat → Nat) : Bool :=
  forceR (powR mul CFSG.KD.FamHNSeed.ONE (mw uK) 10) fun U =>
    Nat.beq (mul U U) CFSG.KD.FamHNSeed.ONE && !Nat.beq U CFSG.KD.FamHNSeed.ONE &&
      !Nat.beq (tr5 (mw [0])) (tr5 U) &&
      ordPK mul CFSG.KD.FamHNSeed.ONE (triM mw (mw [0]) aK₁ aK₂) 19 &&
      ordPK mul CFSG.KD.FamHNSeed.ONE (triM mw U uK₁ uK₂) 19 &&
      ordPK mul CFSG.KD.FamHNSeed.ONE (mul C (cjM mw C cK)) 19

namespace Ck

theorem ok : kitLn mul CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) (mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)) []
      (chk (CFSG.KD.HNPtC.GT 10)) = true := by
  quickRfl

end Ck

end CFSG.KD.W4RowLane.HN

end
