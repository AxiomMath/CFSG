module

public import Certificates.Kernel.LocalComp.L34KuChk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34KuActSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelLC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts.KuAct

theorem kuAct_true : kuActOK = true := by
  unfold kuActOK centR₄ sqC₄
  rw [hR.1, hS.1, cent4, r4_eq]
  refine kuAct_of pinR.canon (CFSG.KS.Raw.Orb.allN_iff.1 kCanon4) (cnRP (by decide)) ?_
  exact scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
    have h1 := kuAll s hs
    unfold ku at h1
    rwa [strictB_app, strictB_app] at h1

end CertificateChecks.KernelLC.L34Scan

end
