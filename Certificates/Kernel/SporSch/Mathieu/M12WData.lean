module

public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Data.Kernel.SporSch.MathieuC3
public import Certificates.Data.CF67M12
public meta import Certificates.Kernel.SporSch.Mathieu.M12Data
public meta import Certificates.Data.Kernel.SporSch.MathieuC3
public meta import Certificates.Data.CF67M12
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12W

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M12OC

meta def evAB (wd : List Int) : Array Nat := evalW 12 #[tAM, tBM] wd

meta def pM : List (List Nat) := Certificates.CF67.M12.pw.map fun wd => (evAB wd).toList

meta def e1M : List (List Nat) := Certificates.CF67.M12.ew.map fun e => (evAB e.1).toList

meta def e2M : List (List Nat) := Certificates.CF67.M12.ew.map fun e => (evAB e.2).toList

meta def SH0 : Array (Array Nat) :=
  strongOf 12 (CFSG.KS.SporSch.MathieuC3.m12Words0.map evAB).toArray
    CFSG.KS.SporSch.MathieuC3.m12ChainWords0

meta def SH1 : Array (Array Nat) :=
  strongOf 12 (CFSG.KS.SporSch.MathieuC3.m12Words1.map evAB).toArray
    CFSG.KS.SporSch.MathieuC3.m12ChainWords1

meta def baseH : Array Nat := #[2, 3]

end CertificateChecks.KernelSporSch.M12W

#kss_packs CertificateChecks.KernelSporSch.M12W.PL 4 CertificateChecks.KernelSporSch.M12W.pM

#kss_packs CertificateChecks.KernelSporSch.M12W.E1L 4 CertificateChecks.KernelSporSch.M12W.e1M

#kss_packs CertificateChecks.KernelSporSch.M12W.E2L 4 CertificateChecks.KernelSporSch.M12W.e2M

#ks_rawchain CertificateChecks.KernelSporSch.M12CH0 12 4 16 CertificateChecks.KernelSporSch.M12W.SH0
  CertificateChecks.KernelSporSch.M12W.baseH 4 CFSG.KS.SporSch.MathieuC3.m12ChainWords0

#ks_rawchain CertificateChecks.KernelSporSch.M12CH1 12 4 16 CertificateChecks.KernelSporSch.M12W.SH1
  CertificateChecks.KernelSporSch.M12W.baseH 4 CFSG.KS.SporSch.MathieuC3.m12ChainWords1

end
