module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Data.Kernel.SporSch.MathieuC3
public import Certificates.Data.Odd87F3M22
public import Certificates.Data.CF67M22
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
public meta import Certificates.Data.Kernel.SporSch.MathieuC3
public meta import Certificates.Data.Odd87F3M22
public meta import Certificates.Data.CF67M22
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22W

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M22OC

meta def evAB (wd : List Int) : Array Nat := evalW 22 #[tAM, tBM] wd

meta def evL (ws : List (List Int)) : List (List Nat) := ws.map fun wd => (evAB wd).toList

meta def ogI3M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsInn_3

meta def ogI5M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsInn_5

meta def ogA3M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsOut1_3

meta def ogA5M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsOut1_5

meta def ogA11M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsOut1_11

meta def ogB3M : List (List Nat) := evL Certificates.Odd87F3.M22.oddWordsOut2_3

meta def a0M : Array Nat := evAB Certificates.CF67.M22.wa

meta def b0M : Array Nat := evAB Certificates.CF67.M22.wb

meta def SH : Array (Array Nat) :=
  strongOf 22 (CFSG.KS.SporSch.MathieuC3.m22Words.map evAB).toArray
    CFSG.KS.SporSch.MathieuC3.m22ChainWords

meta def baseH : Array Nat := #[2, 1]

end CertificateChecks.KernelSporSch.M22W

#kss_packs CertificateChecks.KernelSporSch.M22W.OGI3 5 CertificateChecks.KernelSporSch.M22W.ogI3M

#kss_packs CertificateChecks.KernelSporSch.M22W.OGI5 5 CertificateChecks.KernelSporSch.M22W.ogI5M

#kss_packs CertificateChecks.KernelSporSch.M22W.OGA3 5 CertificateChecks.KernelSporSch.M22W.ogA3M

#kss_packs CertificateChecks.KernelSporSch.M22W.OGA5 5 CertificateChecks.KernelSporSch.M22W.ogA5M

#kss_packs CertificateChecks.KernelSporSch.M22W.OGA11 5
  CertificateChecks.KernelSporSch.M22W.ogA11M

#kss_packs CertificateChecks.KernelSporSch.M22W.OGB3 5 CertificateChecks.KernelSporSch.M22W.ogB3M

#ks_perm CertificateChecks.KernelSporSch.M22W.PA0 5 CertificateChecks.KernelSporSch.M22W.a0M

#ks_perm CertificateChecks.KernelSporSch.M22W.PB0 5 CertificateChecks.KernelSporSch.M22W.b0M

#ks_rawchain CertificateChecks.KernelSporSch.M22CH 22 5 16 CertificateChecks.KernelSporSch.M22W.SH
  CertificateChecks.KernelSporSch.M22W.baseH 3 CFSG.KS.SporSch.MathieuC3.m22ChainWords

end
