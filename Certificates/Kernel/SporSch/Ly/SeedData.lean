
module

public import Certificates.Data.Kernel.SporSch.LySeed
public import Certificates.Data.Kernel.LyOmega.Base
public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.RankThree.Native.LySeedCheckInputs
public import Certificates.Kernel.Misc.Perm.CharsLits
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.SeedGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSporSch.LySd D CertificateChecks.KernelSporSch.LySeedGen.seedStep

#ks_chars_lits CertificateChecks.KernelSporSch.LyFD CFSG.Sporadic.Ly.Native.formDigits
#ks_chars_lits CertificateChecks.KernelSporSch.LyRD CFSG.Sporadic.Ly.Native.rootDigits

namespace CertificateChecks.KernelSporSch.LySd

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KC.LySeed CFSG.KC.LyOm
open CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def pw (M e : Nat) : Nat := powR 5 12 1332 111 8 L H CM RM ONE M e

@[expose] noncomputable def rdig (p : Nat) : Nat :=
  Nat.mod (Nat.sub (Char.toNat (LyRD.chars.getD p '0')) (nat_lit 48)) (nat_lit 5)

@[expose] noncomputable def AB : Nat := mul A B

@[expose] noncomputable def G : Nat := (fun t => mul t t) (mul A B4)

@[expose] noncomputable def Gi : Nat := (fun t => mul t t) (mul B A)

@[expose] noncomputable def XL : Nat := mul (mul (mul A Gi) B) G

@[expose] noncomputable def EL : Nat := mul (mul (mul D.PL D.CL) D.PLT) D.F

theorem ab14 : Nat.beq (pw AB 14) ONE = true := by quickRfl
theorem ab7 : (!Nat.beq (pw AB 7) ONE) = true := by quickRfl
theorem ab2 : (!Nat.beq (pw AB 2) ONE) = true := by quickRfl
theorem nA : (!Nat.beq A ONE) = true := by quickRfl
theorem nB : (!Nat.beq B ONE) = true := by quickRfl
theorem nX : (!Nat.beq XL ONE) = true := by quickRfl

theorem fdig : digLanesK LyFD.chars D.F 12321 = true := by quickRfl
@[expose] noncomputable def noNl (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(Bool.not (Nat.beq (Char.toNat c) (nat_lit 10)), ih)) cs

theorem fnl : noNl LyFD.chars = true := by quickRfl
theorem fsym : symK D.F = true := by quickRfl
theorem vF : vld D.F = true := by quickRfl
theorem vFI : vld D.FI = true := by quickRfl
theorem finv : Nat.beq (mul D.F D.FI) ONE = true := by quickRfl

theorem rlen : Nat.beq LyRD.chars.length 826 = true := by quickRfl
theorem pent : entK D.PL (fun j a => nIf(Nat.blt a 7, rdig (Nat.add (Nat.mul 111 a) j), 0)) = true := by
  quickRfl
theorem cent : entK D.CL (fun a b => nIf(bAnd(Nat.blt a 7, Nat.blt b 7),
    rdig (Nat.add (Nat.add 777 (Nat.mul 7 a)) b), 0)) = true := by quickRfl
theorem ptr : trK D.PL D.PLT = true := by quickRfl
theorem csym : symK D.CL = true := by quickRfl
theorem vPL : vld D.PL = true := by quickRfl
theorem vPLT : vld D.PLT = true := by quickRfl
theorem vCL : vld D.CL = true := by quickRfl
theorem v0 : vld 0 = true := by quickRfl
theorem e2 : Nat.beq (mul EL EL) 0 = true := by quickRfl

end CertificateChecks.KernelSporSch.LySd

end
