module

public import Certificates.Kernel.Sporadic.OddCore.S8147D
public import Certificates.Data.Kernel.Spor.HNAOrb
public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.HNA
open CertificateChecks.KernelSpor

theorem hC3 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFC3.G k)) && Nat.beq (SFC3.T 0) (pidn 1782 11) && Nat.beq (SFC3.C 0) 1 &&
    Nat.beq (SFC3.C 75) 3600) = true := by quickRfl

theorem dC3 : distinctK 3600 SFC3.T SFC3.S = true := by quickRfl

theorem kC3 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 3600 SFC3.T (listUp SFC3.SKT 3600) = true := by
  quickRfl

theorem pC3 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFC3.G k)
    (pinvS 1782 11 (mask 11) (SFC3.G k))) = true := by quickRfl

@[expose] noncomputable def c3s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFC3.T 48 s, runSl 1782 11 2 SFC3.G SFC3.T SFC3.E 48 SFC3.C s)

end CertificateChecks.KernelSpor.S8147

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.S8147.C3K CertificateChecks.KernelSpor.S8147.c3s 0 75
#kqb_all CertificateChecks.KernelSpor.S8147.C3K CertificateChecks.KernelSpor.S8147.c3s 75

end
