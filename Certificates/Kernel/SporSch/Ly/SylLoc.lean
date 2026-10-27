module

public import Certificates.Kernel.SporSch.Ly.SylChk
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PackWord
meta import Certificates.Kernel.SporSch.Ly.GenLy
meta import CFSG.Sporadic.Schreier.LyCheckSylow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySL

open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
meta def wiM : List Nat :=
  let b4 := powM 5 111 (matB ()) 4
  [CFSG.KS.SporSch.LyGen.packM (invM 5 111 (evalWordM seedM (seedMInv b4) (fusionWord ())))]

end CertificateChecks.KernelSporSch.LySL

#knatlist CertificateChecks.KernelSporSch.LySL.WIL CertificateChecks.KernelSporSch.LySL.wiM

#ks_chars CertificateChecks.KernelSporSch.LyCJ CFSG.Sporadic.LySchreier.Native.involutionConjugatorsTxt

namespace CertificateChecks.KernelSporSch.LySL

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def WI : Nat := List.headD WIL 0

@[expose] noncomputable def WW : Nat := wordR 5 12 1332 111 8 L H CM RM GS GSI ONE [1, 2]

@[expose] noncomputable def X : Nat := mul (mul WW A) WI

@[expose] noncomputable def ZX : Nat := mul A X

@[expose] noncomputable def XF : Nat := mul X (LySy.E 113)

@[expose] noncomputable def GG : Nat :=
  mul (powR 5 12 1332 111 8 L H CM RM ONE XF 7) (powR 5 12 1332 111 8 L H CM RM ONE ZX 4)

theorem vW : bAnd(vld WW, bAnd(vld WI, bAnd(vld X, bAnd(vld ZX, bAnd(vld XF, vld GG))))) = true := by
  quickRfl
theorem wwi : Nat.beq (mul WW WI) ONE = true := by quickRfl
theorem z9 : Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE ZX 9) ONE = true := by quickRfl
theorem x15 : Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE XF 15) ONE = true := by quickRfl
theorem gA : Nat.beq (mul GG A) (mul (LySy.E 113) GG) = true := by quickRfl
theorem h3 : Nat.beq (mul (CI 11) (mul (CI 11) (CI 11))) ONE = true := by quickRfl
theorem hne : Bool.not (Nat.beq (CI 11) ONE) = true := by quickRfl

@[expose] noncomputable def getN (l : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun i' _ => ih i') i) l t

@[expose] noncomputable def getC (l : List (Nat × List Int)) (t : Nat) : Nat × List Int :=
  List.rec (motive := fun _ => Nat → Nat × List Int) (fun _ => (0, []))
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat × List Int) x (fun i' _ => ih i') i) l t

@[expose] noncomputable def hqQ (t : Nat) : Bool :=
  strictB (getN qIndices.toList t) (fun q =>
    Nat.beq (mul (CI 11) (LySy.E q)) (mul (LySy.E q) (CI 11)))

@[expose] noncomputable def cjQ (t : Nat) : Bool :=
  bIf(Nat.blt t 58, Prod.rec (motive := fun _ => Bool) (fun k w =>
    strictB (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE w) (fun M =>
      Nat.beq (mul M (LySy.E 113)) (mul (LySy.E k) M))) (getC LySt.CL t), true)

end CertificateChecks.KernelSporSch.LySL

#kly_chain CertificateChecks.KernelSporSch.LySL hq CertificateChecks.KernelSporSch.LySL.hqQ 16 4
#kly_chain CertificateChecks.KernelSporSch.LySL cj CertificateChecks.KernelSporSch.LySL.cjQ 15 4

namespace CertificateChecks.KernelSporSch.LySL

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS

theorem qw0 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE [3, 1, 3, 2, 1])
    (LySy.E 155) = true := by quickRfl
theorem qw1 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE [1, 3, 4, 1])
    (LySy.E 101) = true := by quickRfl
theorem qw2 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE [4, 3, 2])
    (LySy.E 49) = true := by quickRfl
theorem qw3 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE [2, 3])
    (LySy.E 18) = true := by quickRfl

theorem conv : convK LyCJ.chars LySt.CL = true := by quickRfl

theorem clLen : LySt.CL.length = 58 := by decide

end CertificateChecks.KernelSporSch.LySL

end
