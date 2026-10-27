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

theorem hC1 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFC1.G k)) && Nat.beq (SFC1.T 0) (pidn 1782 11) && Nat.beq (SFC1.C 0) 1 &&
    Nat.beq (SFC1.C 15) 600) = true := by quickRfl
theorem dC1 : distinctK 600 SFC1.T SFC1.S = true := by quickRfl
theorem kC1 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 600 SFC1.T (listUp SFC1.SKT 600) = true := by
  quickRfl
theorem pC1 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFC1.G k)
    (pinvS 1782 11 (mask 11) (SFC1.G k))) = true := by quickRfl

theorem hC2 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFC2.G k)) && Nat.beq (SFC2.T 0) (pidn 1782 11) && Nat.beq (SFC2.C 0) 1 &&
    Nat.beq (SFC2.C 15) 600) = true := by quickRfl
theorem dC2 : distinctK 600 SFC2.T SFC2.S = true := by quickRfl
theorem kC2 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 600 SFC2.T (listUp SFC2.SKT 600) = true := by
  quickRfl
theorem pC2 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFC2.G k)
    (pinvS 1782 11 (mask 11) (SFC2.G k))) = true := by quickRfl

theorem hC5 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFC5.G k)) && Nat.beq (SFC5.T 0) (pidn 1782 11) && Nat.beq (SFC5.C 0) 1 &&
    Nat.beq (SFC5.C 15) 600) = true := by quickRfl
theorem dC5 : distinctK 600 SFC5.T SFC5.S = true := by quickRfl
theorem kC5 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 600 SFC5.T (listUp SFC5.SKT 600) = true := by
  quickRfl
theorem pC5 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFC5.G k)
    (pinvS 1782 11 (mask 11) (SFC5.G k))) = true := by quickRfl

@[expose] noncomputable def c1s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFC1.T 40 s, runSl 1782 11 2 SFC1.G SFC1.T SFC1.E 40 SFC1.C s)

@[expose] noncomputable def c2s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFC2.T 40 s, runSl 1782 11 2 SFC2.G SFC2.T SFC2.E 40 SFC2.C s)

@[expose] noncomputable def c5s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFC5.T 40 s, runSl 1782 11 2 SFC5.G SFC5.T SFC5.E 40 SFC5.C s)

end CertificateChecks.KernelSpor.S8147

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.S8147.C1K CertificateChecks.KernelSpor.S8147.c1s 0 15
#kqb_all CertificateChecks.KernelSpor.S8147.C1K CertificateChecks.KernelSpor.S8147.c1s 15
#kqb_range CertificateChecks.KernelSpor.S8147.C2K CertificateChecks.KernelSpor.S8147.c2s 0 15
#kqb_all CertificateChecks.KernelSpor.S8147.C2K CertificateChecks.KernelSpor.S8147.c2s 15
#kqb_range CertificateChecks.KernelSpor.S8147.C5K CertificateChecks.KernelSpor.S8147.c5s 0 15
#kqb_all CertificateChecks.KernelSpor.S8147.C5K CertificateChecks.KernelSpor.S8147.c5s 15

end
