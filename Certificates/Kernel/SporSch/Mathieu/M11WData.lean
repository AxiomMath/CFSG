module

public import Certificates.Kernel.SporSch.Mathieu.M11Data
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public import Certificates.Data.Kernel.SporSch.MathieuC3
public import Certificates.Data.Odd87F3M11
public import Certificates.Data.CF67M11
public meta import Certificates.Kernel.SporSch.Mathieu.M11Data
public meta import Certificates.Data.Kernel.SporSch.MathieuC3
public meta import Certificates.Data.Odd87F3M11
public meta import Certificates.Data.CF67M11
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11W

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M11OC

meta def evAB (wd : List Int) : Array Nat := evalW 11 #[tAM, tBM] wd

meta def ogM : List (List Nat) := Certificates.Odd87F3.M11.oddWords.map fun wd => (evAB wd).toList

meta def a0M : Array Nat := evAB Certificates.CF67.M11.wa

meta def b0M : Array Nat := evAB Certificates.CF67.M11.wb

meta def SH : Array (Array Nat) :=
  strongOf 11 (CFSG.KS.SporSch.MathieuC3.m11Words.map evAB).toArray
    CFSG.KS.SporSch.MathieuC3.m11ChainWords

meta def baseH : Array Nat := #[2, 0]

end CertificateChecks.KernelSporSch.M11W

#kss_packs CertificateChecks.KernelSporSch.M11W.OG 4 CertificateChecks.KernelSporSch.M11W.ogM

#ks_perm CertificateChecks.KernelSporSch.M11W.A0 4 CertificateChecks.KernelSporSch.M11W.a0M

#ks_perm CertificateChecks.KernelSporSch.M11W.B0 4 CertificateChecks.KernelSporSch.M11W.b0M

#ks_rawchain CertificateChecks.KernelSporSch.M11CH 11 4 16 CertificateChecks.KernelSporSch.M11W.SH
  CertificateChecks.KernelSporSch.M11W.baseH 3 CFSG.KS.SporSch.MathieuC3.m11ChainWords

#kss_classes2 CertificateChecks.KernelSporSch.M11WCK 11 4 CertificateChecks.KernelSporSch.M11OC.tAM
  CertificateChecks.KernelSporSch.M11OC.tBM CertificateChecks.KernelSporSch.M11OC.tA
  CertificateChecks.KernelSporSch.M11OC.tB CertificateChecks.KernelSporSch.M11OC.repsM 2 400

end
