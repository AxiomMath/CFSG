module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Data.Kernel.SporSch.M23C3
public import Certificates.Data.Odd87F3M23
public import Certificates.Data.CF67M23
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
public meta import Certificates.Data.Kernel.SporSch.M23C3
public meta import Certificates.Data.Odd87F3M23
public meta import Certificates.Data.CF67M23
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23W

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M23OC

meta def evAB (wd : List Int) : Array Nat := evalW 23 #[tAM, tBM] wd

meta def og3M : List (List Nat) := Certificates.Odd87F3.M23.oddWords3.map fun wd => (evAB wd).toList

meta def og5M : List (List Nat) := Certificates.Odd87F3.M23.oddWords5.map fun wd => (evAB wd).toList

meta def a0M : Array Nat := evAB Certificates.CF67.M23.wa

meta def b0M : Array Nat := evAB Certificates.CF67.M23.wb

meta def SH : Array (Array Nat) :=
  strongOf 23 (CFSG.KS.SporSch.M23C3.c3Words.map evAB).toArray
    CFSG.KS.SporSch.M23C3.c3ChainWords

meta def baseH : Array Nat := #[3, 5]

end CertificateChecks.KernelSporSch.M23W

#kss_packs CertificateChecks.KernelSporSch.M23W.OG3 5 CertificateChecks.KernelSporSch.M23W.og3M

#kss_packs CertificateChecks.KernelSporSch.M23W.OG5 5 CertificateChecks.KernelSporSch.M23W.og5M

#ks_perm CertificateChecks.KernelSporSch.M23W.A0 5 CertificateChecks.KernelSporSch.M23W.a0M

#ks_perm CertificateChecks.KernelSporSch.M23W.B0 5 CertificateChecks.KernelSporSch.M23W.b0M

#ks_rawchain CertificateChecks.KernelSporSch.M23CH 23 5 16 CertificateChecks.KernelSporSch.M23W.SH
  CertificateChecks.KernelSporSch.M23W.baseH 3 CFSG.KS.SporSch.M23C3.c3ChainWords

end
