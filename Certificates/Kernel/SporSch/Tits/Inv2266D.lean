module

public import Certificates.Kernel.SporSch.Tits.Abel2261
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.SporSch.Tits.GenList
public import Certificates.Kernel.SporSch.Tits.GenAll5
public import CFSG.Certificates.Kernel.SporSch.TitsInvSound
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsT 11 CFSG.Sporadic.Schreier.Tits.titsTArr
#kst_plist CertificateChecks.KernelSporSch.TitsIC 11 CFSG.Sporadic.Schreier.Tits.titsInvConj
#kst_plist CertificateChecks.KernelSporSch.TitsEX 11 CFSG.Sporadic.Schreier.Tits.titsExcl

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def P8 (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(sqGR (CertificateChecks.KernelMisc.TitsText.F 1) t0 t1 t2 t3 t4, false, true)

@[expose] noncomputable def Q8 : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => P8

@[expose] noncomputable def P3 (t0 t1 t2 t3 t4 : Nat) : Bool :=
  strictB (gpt 11 (mask 11) t0 t1 t2 t3 t4 (nat_lit 1754)) (fun a =>
  strictB (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) TitsT (nat_lit 1754))) (fun b =>
  allL (fun y => bIf(Nat.beq (pg 11 (mask 11) y a) b,
    bIf(conjPts 1755 11 (mask 11) TitsT y t0 t1 t2 t3 t4, false, true), true)) TitsEX))

@[expose] noncomputable def Q3 : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => P3

#kst_all5 CertificateChecks.KernelSporSch.TitsS8 1755 11 8 2 TitsS.LR TitsS.TR Q8
#kst_all5 CertificateChecks.KernelSporSch.TitsH3 1755 11 10 8 TitsH.LR TitsH.TR Q3

end CertificateChecks.KernelSporSch.TitsInv

end
