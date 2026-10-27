module

public import Certificates.Kernel.HN1408.TfData
public import Certificates.Kernel.HN1408.TableIData
public import Certificates.Kernel.HN1408.SpecDefs
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

@[expose] noncomputable def fOf (F : Nat → Nat) (s r h : Nat) : Nat := F (Nat.add (Nat.mul s r) h)

@[expose] noncomputable def tfOne (r : Nat) : Bool :=
  strictB (TfO.cnt r) fun co =>
  bAnd(allN 2 (fun j => bAnd(Nat.beq (fOf TfO.G TfO.ts r j) (WK (classz₁.centGens.getD j [])),
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) (fOf TfO.GI TfO.ts r j),
        invEqK 1408 11 (mask 11) (1408 * 11) (fOf TfO.G TfO.ts r j) (fOf TfO.GI TfO.ts r j)))),
  bAnd(Nat.beq (TfO.R r) (TI4.T (Nat.add r 1)),
  bAnd(penumHdK (TfO.R r) co 100 (fOf TfO.T TfO.ts r) (fOf TfO.PL TfO.rr r),
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true (fOf TfO.G TfO.ts r) (fOf TfO.GI TfO.ts r) 2 co
      (fOf TfO.T TfO.ts r) (fOf TfO.PL TfO.rr r) (fOf TfO.POS TfO.pr r) (fOf TfO.SRT TfO.rr r)
      (fOf TfO.SRI TfO.rr r) 0 co,
  bAnd(slK co (hsortPtK 1408 11 (mask 11) co (fOf TfO.T TfO.ts r) (fOf TfO.HS TfO.rr r)
      (fOf TfO.HSI TfO.rr r)) 0 co,
  strictB (TfS.cnt r) fun cs =>
  bAnd(allN co (fun j => bAnd(Nat.beq (fOf TfS.G TfS.ts r j) idK,
      Nat.beq (fOf TfS.GI TfS.ts r j) (fOf TfO.T TfO.ts r j))),
  bAnd(Nat.beq cs 16,
  bAnd(penumHdK idK cs 100 (fOf TfS.T TfS.ts r) (fOf TfS.PL TfS.rr r),
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true (fOf TfS.G TfS.ts r) (fOf TfS.GI TfS.ts r) co cs
      (fOf TfS.T TfS.ts r) (fOf TfS.PL TfS.rr r) (fOf TfS.POS TfS.pr r) (fOf TfS.SRT TfS.rr r)
      (fOf TfS.SRI TfS.rr r) 0 cs,
    slK cs (hsortPtK 1408 11 (mask 11) cs (fOf TfS.T TfS.ts r) (fOf TfS.HS TfS.rr r)
      (fOf TfS.HSI TfS.rr r)) 0 cs)))))))))

@[expose] noncomputable def tfZ : List Nat := classz₁.centGens.map WK
@[expose] noncomputable def tfZR : List Nat := (classz₁.centGens.map List.reverse).map WK

@[expose] noncomputable def tfCommK (p : List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat)) :
    Bool :=
  strictB (specK tfZ p.1) fun U => strictB (specK tfZ p.2.1) fun V =>
  strictB (specK tfZR p.1.reverse) fun UI => strictB (specK tfZR p.2.1.reverse) fun VI =>
  bAnd(invEqK 1408 11 (mask 11) (1408 * 11) U UI, bAnd(invEqK 1408 11 (mask 11) (1408 * 11) V VI,
    Nat.beq (pc (pc (pc U V) UI) VI) (specK tfZ p.2.2)))

theorem tfkOne : allN 15 tfOne = true := by quickRfl

theorem tfkComm : tfComm.all tfCommK = true := by quickRfl

end CFSG.KD.HN1408

end
