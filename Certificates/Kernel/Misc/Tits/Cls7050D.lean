
module

public import Certificates.Kernel.EvenBN.CNtAux
public import Certificates.Kernel.Sporadic.Tits.Sift2264
public import Certificates.Kernel.SporSch.Tits.GenList
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public meta import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TY CFSG.Quasithin.RuRank3.titsY12Text
#kmisc_hexflat CertificateChecks.KernelMisc.TY CFSG.Quasithin.RuRank3.titsY12Text 3 1755 11 1
#ks_chars CertificateChecks.KernelMisc.TX CFSG.Quasithin.RuRank3.titsX13Text
#kmisc_hexflat CertificateChecks.KernelMisc.TX CFSG.Quasithin.RuRank3.titsX13Text 3 1755 11 1
#ks_chars CertificateChecks.KernelMisc.TR CFSG.Quasithin.RuRank3.titsRepsText
#kmisc_hexflat CertificateChecks.KernelMisc.TR CFSG.Quasithin.RuRank3.titsRepsText 3 1755 11 30
#ks_chars CertificateChecks.KernelMisc.TK CFSG.Quasithin.RuRank3.titsK0Text
#kmisc_hexflat CertificateChecks.KernelMisc.TK CFSG.Quasithin.RuRank3.titsK0Text 3 1755 11 5

namespace CertificateChecks.KernelMisc.Tits7050

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

meta def wOf (c : Array Nat) : Nat :=
  if !isInvolA c then 0 else if eqA 1755 c titsTArr then 1 else
    ((List.range 12).find? fun k =>
      let y := powArr 1755 titsY12Arr k
      (List.range 30).any fun i =>
        eqA 1755 (compA 1755 (compA 1755 y c) (invCand 1755 y)) (titsRepArr i)).getD 13 + 2

meta def wM : List Nat := titsCNt.map fun c => wOf c * 16 + wOf (compA 1755 titsAuxArr c)

meta def yPows : List (Array Nat) := (List.range 12).map (powArr 1755 titsY12Arr)
meta def yInvs : List (Array Nat) := yPows.map (invCand 1755)

end CertificateChecks.KernelMisc.Tits7050

#kss_natlist CertificateChecks.KernelMisc.Tits7050.W CertificateChecks.KernelMisc.Tits7050.wM
#kst_plist CertificateChecks.KernelMisc.Tits7050.YL 11 CertificateChecks.KernelMisc.Tits7050.yPows
#kst_plist CertificateChecks.KernelMisc.Tits7050.YIL 11 CertificateChecks.KernelMisc.Tits7050.yInvs

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch CertificateChecks.KernelEvenBN

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def pw (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1755 11) (fun _ acc => pc p acc) k

@[expose] noncomputable def Aux : Nat := TAux.F 0
@[expose] noncomputable def Y : Nat := TY.F 0
@[expose] noncomputable def X : Nat := TX.F 0
@[expose] noncomputable def R (i : Nat) : Nat := TR.F i

@[expose] noncomputable def notInv (P : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) ((List.range 1755).any fun x =>
      Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq (pg 11 (mask 11) P (pg 11 (mask 11) P x)) x))
    true (Nat.beq P (pidn 1755 11))

@[expose] noncomputable def clsK (P w : Nat) : Bool :=
  bIf(Nat.beq w 0, notInv P, bIf(Nat.beq w 1, Nat.beq P TitsT,
    strictB (pc (pc (CFSG.KS.Mathieu.nget YL (Nat.sub w 2)) P)
      (CFSG.KS.Mathieu.nget YIL (Nat.sub w 2))) fun x =>
      bAnd(Nat.blt (Nat.sub w 2) 12, (List.range 30).any fun i => Nat.beq x (R i))))

@[expose] noncomputable def cls2 (k w : Nat) : Bool :=
  strictB (PN k) fun P => bAnd(clsK P (Nat.div w 16), strictB (pc Aux P) fun Q => clsK Q (Nat.mod w 16))

@[expose] noncomputable def chkL (W : Nat → Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih j => bAnd(cls2 k (W j), ih (Nat.succ j)))

theorem perms : bAnd(permC Aux, bAnd(permC Y, bAnd(permC X, permC TitsT))) = true := by quickRfl

theorem permR : allN 30 (fun i => permC (R i)) = true := by quickRfl

theorem permK : allN 5 (fun j => permC (TK.F j)) = true := by quickRfl

theorem auxA : bAnd(siftD (pc Aux (GI 1)), permC (pc Aux (GI 1))) = true := by quickRfl

theorem auxD : siftD Aux = false := by decide +kernel

theorem auxT : Nat.beq (pc Aux TitsT) (pc TitsT Aux) = true := by quickRfl

theorem yA : bAnd(siftD (pc Y (GI 1)), permC (pc Y (GI 1))) = true := by quickRfl

theorem yT : Nat.beq (pc Y TitsT) (pc TitsT Y) = true := by quickRfl

theorem yX : Nat.beq (pc Y X) (pc (pw X 11) Y) = true := by quickRfl

theorem yPow : allN 12 (fun k => bAnd(Nat.beq (CFSG.KS.Mathieu.nget YL k) (pw Y k),
    bAnd(Nat.beq (CFSG.KS.Mathieu.nget YIL k) (pinvS 1755 11 (mask 11) (CFSG.KS.Mathieu.nget YL k)),
      permC (CFSG.KS.Mathieu.nget YL k)))) = true := by quickRfl

theorem tX : Nat.beq (pc (pc (pc TitsT X) TitsT) X) (pidn 1755 11) = true := by quickRfl

theorem k0X : bAnd(Nat.beq (TK.F 0) X, Nat.beq (TK.F 1) TitsT) = true := by quickRfl

theorem k2A : siftD (TK.F 2) = true := by quickRfl

end CertificateChecks.KernelMisc.Tits7050

end
