module

public import Certificates.Kernel.OmegaEight.Quat125K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

@[expose] noncomputable def q125AllL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def q125ClAt (U V Ui Vi X0 x : Nat) : Bool :=
  bAnd(e4Mem e4L (pc U x), bAnd(e4Mem e4L (pc V x), bAnd(e4Mem e4L (pc Ui x),
    bAnd(e4Mem e4L (pc Vi x), bIf(Nat.beq (pc x x) pid,
      bIf(Nat.beq x pid, true, Nat.beq x X0), true)))))

theorem kLet125 : strictB (gtK (fun l => AP.S l) 8) (fun GT => allN 8 fun l => allN 360 fun p =>
    Nat.beq (letK GT (Nat.succ l) p) (pg 9 511 (AP.S l) p)) = true := by quickRfl

theorem kInvol125 : allN 8 (fun l => Nat.beq (pc (AP.S l) (AP.S l)) pid) = true := by quickRfl

theorem kFix125 : strictB e4U (fun U => strictB om0V fun V => strictB (fixMK U V 360) fun F =>
    allN 360 fun q => bIf(bitK F q,
      bAnd(Nat.beq (pg 9 511 U q) q, Nat.beq (pg 9 511 V q) q),
      bIf(bAnd(Nat.beq (pg 9 511 U q) q, Nat.beq (pg 9 511 V q) q), false, true))) = true := by
  quickRfl

theorem kK0Cl125 : bAnd(e4Mem e4L pid, strictB (pinv e4U) fun Ui => strictB (pinv om0V) fun Vi =>
    q125AllL e4L (q125ClAt e4U om0V Ui Vi (mainK 0))) = true := by quickRfl

theorem kRow1W125 : Nat.beq (rowW (RT 1)) 1 = true := by quickRfl

theorem neg125Let : Bool.not (strictB (gtK (fun l => AP.S (Nat.succ l)) 8) (fun GT =>
    allN 8 fun l => allN 360 fun p =>
      Nat.beq (letK GT (Nat.succ l) p) (pg 9 511 (AP.S l) p))) = true := by quickRfl

theorem neg125Invol : Bool.not (Nat.beq (pc e4U e4U) pid) = true := by quickRfl

theorem neg125Fix : Bool.not (strictB e4U (fun U => strictB om0V fun V =>
    strictB (fixMK U V 240) fun F => allN 360 fun q => bIf(bitK F q,
      bAnd(Nat.beq (pg 9 511 U q) q, Nat.beq (pg 9 511 V q) q),
      bIf(bAnd(Nat.beq (pg 9 511 U q) q, Nat.beq (pg 9 511 V q) q), false, true)))) = true := by
  quickRfl

theorem neg125Cl : Bool.not (strictB (pinv e4U) fun Ui => strictB (pinv om0V) fun Vi =>
    q125AllL (e4L.take 7) (fun x => bAnd(e4Mem (e4L.take 7) (pc e4U x),
      e4Mem (e4L.take 7) (pc om0V x)))) = true := by quickRfl

theorem neg125Inv0 : Bool.not (strictB (pinv e4U) fun Ui => strictB (pinv om0V) fun Vi =>
    q125AllL e4L (q125ClAt e4U om0V Ui Vi e4U)) = true := by quickRfl

end CertificateChecks.KernelO8.Q125

end
