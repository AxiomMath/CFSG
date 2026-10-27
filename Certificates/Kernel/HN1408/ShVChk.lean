module

public import Certificates.Kernel.HN1408.ShVData
public import Certificates.Kernel.HN1408.CayleyDefs
public import Certificates.Kernel.HN1408.M11Lem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def shvD5 : Bool := d5Words.all fun w => commP (WK w) (WK fix5C.rep)

@[expose] noncomputable def shvConj (C CI X Z : Nat) : Bool :=
  bAnd(canonK 1408 11 (mask 11) (1408 * 11) CI, bAnd(invEqK 1408 11 (mask 11) (1408 * 11) C CI,
    Nat.beq (pc (pc C X) CI) Z))

@[expose] noncomputable def shvUK (u r a z C CI : Nat) : Bool :=
  bAnd(Nat.beq (ppK u 2) idK, bAnd(bIf(Nat.beq u idK, false, true),
    bAnd(bIf(Nat.beq u a, false, true), bAnd(commP u r, shvConj C CI z u))))

@[expose] noncomputable def shvU : Bool :=
  shvUK (WK u0Word) (WK fix5B.rep) (WK wordA) (WK wordZ₁) (WK c0Word) (ShVCI 0)

@[expose] noncomputable def shvA8K (p r b : Nat) (CK CI : Nat → Nat) : Bool :=
  bAnd(Nat.beq (ppK p 5) idK, bAnd(bIf(Nat.beq p idK, false, true),
    bAnd(commP p b, allN 4 fun k => shvConj (CK k) (CI (k + 1)) r (ppK p (k + 1)))))

@[expose] noncomputable def shvA8 : Bool :=
  shvA8K (WK rpWord) (WK fix5C.rep) (WK wordB) (fun k => WK (ckWords.getD k [])) ShVCI

theorem shvkHd : cyHd d5Words 120 capS ShVD5.G ShVD5.GI ShVD5I ShVD5.T ShVD5.PL ShVD5.cnt = true := by
  quickRfl

theorem shvkRec : cyRec d5Words.length ShVD5.G ShVD5.GI ShVD5I ShVD5.T ShVD5.PL ShVD5.POS ShVD5.SRT
    ShVD5.SRI ShVD5.HS ShVD5.HSI ShVD5Cl ShVD5.cnt = true := by
  quickRfl

theorem shvkCay : cayK sl25Mul 126 [541, 537] d5Words.length ShVD5.cnt ShVD5.PL ShVD5Cl
    (cayCodes sl25Mul 126 [541, 537] ShVD5.PL ShVD5.cnt) = true := by
  quickRfl

theorem shvkD5 : shvD5 = true := by quickRfl

theorem shvkU : shvU = true := by quickRfl

theorem shvkA8 : shvA8 = true := by quickRfl

end CFSG.KD.HN1408

end
