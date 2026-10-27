module

public import Certificates.Kernel.SuzPump.PumpPair
public import Certificates.Data.Kernel.Spor.HNAOrb
public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzPump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.HNA
open CertificateChecks.KernelSpor

theorem hPP : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SPP.G k)) && Nat.beq (SPP.T 0) (pidn 1782 11) && Nat.beq (SPP.C 0) 1 &&
    Nat.beq (SPP.C 126) 7560) = true := by quickRfl

theorem dPP : distinctK 7560 SPP.T SPP.S = true := by quickRfl

theorem kPP : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 7560 SPP.T (listUp SPP.SKT 7560) = true := by
  quickRfl

theorem pPP : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SPP.G k)
    (pinvS 1782 11 (mask 11) (SPP.G k))) = true := by quickRfl

@[expose] noncomputable def pps (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SPP.T 60 s, runSl 1782 11 2 SPP.G SPP.T SPP.E 60 SPP.C s)

end CertificateChecks.KernelSuzPump

set_option Elab.async false

#kqb_range CertificateChecks.KernelSuzPump.PPK CertificateChecks.KernelSuzPump.pps 0 126
#kqb_all CertificateChecks.KernelSuzPump.PPK CertificateChecks.KernelSuzPump.pps 126

end
