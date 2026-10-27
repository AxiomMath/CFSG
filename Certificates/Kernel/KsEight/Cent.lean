module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.KsEight.Data
public import Certificates.Data.Kernel.Spor.CentBoundPow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKsEight

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def RSj (j : Nat) : Nat → Nat := fun l => CR (Nat.add (Nat.mul 3 j) l)

@[expose] noncomputable def OMj (j : Nat) : Nat → Nat → Nat :=
  fun l i => OM (Nat.add (Nat.mul 9 j) (Nat.add (Nat.mul 3 l) i))

@[expose] noncomputable def ubPowOK (j c : Nat) : Bool :=
  bAnd(ubPowOkK 820 10 (mask 10) C.S C.SI 7 C.BP 3 3 (RSj j) (OMj j),
    Nat.beq (ubPowProdK 820 10 (mask 10) (820 * 10) C.LR C.TRI 3 3 (RSj j) (OMj j)) c)

@[expose] noncomputable def inCentK (r g : Nat) : Bool :=
  bAnd(cK g, bAnd(inPK g, Nat.beq (pc g r) (pc r g)))

@[expose] noncomputable def lbTowK (r : Nat) (G L : Nat → Nat) (nh nl c : Nat) : Bool :=
  bAnd(allN nh (fun l => inCentK r (G l)),
  bAnd(towerK 820 10 (mask 10) G L nh nl, Nat.beq (towerProdK 10 (mask 10) L nl) c))

@[expose] noncomputable def qElK (i : Nat) : Bool :=
  strictB (QE i) (fun q => bAnd(
    bIf(Nat.beq i (nat_lit 0), Nat.beq q (pidn 820 10),
      strictB (QP i) (fun pa => bAnd(Nat.blt (Nat.div pa 3) i,
        Nat.beq q (pc (QE (Nat.div pa 3)) (QG (Nat.mod pa 3)))))),
    bAnd(allN 3 (fun a => strictB (QX (Nat.add (Nat.mul 3 i) a)) (fun x =>
      bAnd(Nat.blt x 16, Nat.beq (pc q (QG a)) (QE x)))),
    allN i (fun k => bIf(Nat.beq q (QE k), false, true)))))

@[expose] noncomputable def cwK (j e : Nat) : Bool :=
  strictB (CW (Nat.add (Nat.mul 2 j) e)) (fun w => strictB (RK j) (fun r =>
    bAnd(cK w, bAnd(Nat.beq (pc w r) (pc r w), inPK (pc w (TKI (Nat.add 2 (Nat.mul 3 e))))))))

@[expose] noncomputable def dwK (i : Nat) : Bool :=
  strictB (DW i) (fun g => bAnd(cK g, bAnd(inPK g,
    Nat.beq (pc g (pc (CU43T 0) (RK (Nat.add i 2)))) (pc (RK (Nat.add i 5)) (pc g (CU43T 0))))))

theorem kcU0 : ubPowOK 0 8 = true := by quickRfl
theorem kcU1 : ubPowOK 1 8 = true := by quickRfl
theorem kcU2 : ubPowOK 2 8 = true := by quickRfl
theorem kcU3 : ubPowOK 3 16 = true := by quickRfl
theorem kcU4 : ubPowOK 4 64 = true := by quickRfl

theorem kcL0 : lbTowK (CR 0) H0 L0 2 2 8 = true := by quickRfl
theorem kcL1 : lbTowK (CR 3) H1 L1 3 2 8 = true := by quickRfl
theorem kcL3 : lbTowK (CR 9) H3 L3 3 2 16 = true := by quickRfl

theorem kcQ : bAnd(allN 3 (fun a => inCentK (CR 12) (QG a)), allN 16 qElK) = true := by quickRfl

theorem kcE3 : strictB (E3 0) (fun g => bAnd(inCentK (CR 12) g,
    bAnd(Nat.beq (pc g (pc g g)) (pidn 820 10), bIf(Nat.beq g (pidn 820 10), false, true)))) = true := by
  quickRfl

theorem kcW : allN 8 (fun j => allN 2 (cwK j)) = true := by quickRfl

theorem kcD : allN 3 dwK = true := by quickRfl

end CertificateChecks.KernelKsEight

end
