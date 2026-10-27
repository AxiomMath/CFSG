module

public import Certificates.Kernel.S63K.HBind
public import Certificates.Kernel.S63K.AData
public import CFSG.Certificates.Kernel.S63K.BfsSound
public import Certificates.Data.Kernel.S63K.Sorted
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.HD

open CFSG.KC.S63K CFSG.KS.SporSch.M24 CFSG.KC.Enum CFSG.KS CFSG.LargeExtraspecial.S63

@[expose] noncomputable def onK (l p : ℕ) : Bool :=
  Nat.beq p (lp l 0) || Nat.beq p (lp l 1) || Nat.beq p (lp l 2)

@[expose] noncomputable def stabK (w : List ℕ) (l : ℕ) : Bool :=
  onK l (ptW w (lp l 0)) && onK l (ptW w (lp l 1)) && onK l (ptW w (lp l 2))

@[expose] noncomputable def mw (A B : ℕ) : ℕ := CFSG.KC.F2W.mulW 24 A B

@[expose] noncomputable def cj (i : ℕ) : ℕ := mw (mw (mw G3 idP) (TP i)) (mw G3 idP) % 2 ^ 576

@[expose] noncomputable def autK (i : ℕ) : Bool :=
  (fun m => Nat.beq m 0 || (Nat.beq m 1 && Nat.beq (memS AD.QP AD.QS 512 (TP i)) 1))
    (memS TP TS 4096 (cj i))

@[expose] noncomputable def autC (b : ℕ) : Bool := allN 64 fun r => autK (64 * b + r)

theorem cw : (cWords.length == 4 && cWords.all (fun w => w.all fun k => decide (k < 8))) = true := by
  decide +kernel

theorem lineK : (allN 2457 fun l => Nat.beq l 0 ||
    (List.range 4).any fun k => !stabK (cWords.getD k []) l) = true := by
  quickRfl

theorem fix0 : Nat.beq (im 3 0) 0 = true := by quickRfl

theorem repT : bfsK (stepK UG) TP TPar TLab TW TS 4 (4096 + 1) 4096 idP = true := by quickRfl

#kc_each CertificateChecks.KernelS63.HD.autC 0 64

theorem neg : bAnd(bIf(Nat.beq (memS TP TS 4096 (TP 4095 + 1)) 1, false, true),
    bAnd(Nat.beq (memS TP TS 4096 (TP 17)) 1, stabK (cWords.getD 0 []) 0)) = true := by
  quickRfl

end CertificateChecks.KernelS63.HD

end
