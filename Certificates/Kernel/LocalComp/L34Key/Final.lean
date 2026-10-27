module

public import Certificates.Kernel.LocalComp.L34Key.Chk0
public import Certificates.Kernel.LocalComp.L34Key.Chk1
public import Certificates.Kernel.LocalComp.L34Key.Small
public import Certificates.Kernel.LocalComp.L34Cert
public import Certificates.Kernel.LocalComp.L34ScanFinal
public import CFSG.Certificates.Kernel.L34KeySound
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34Key.key9304All CertificateChecks.KernelLC.L34Key.key9304 180

namespace CertificateChecks.KernelLC.L34Key

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.L34Key CFSG.KC.L34KSnd
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ClassicalInvolution.Nobq

theorem l34CQ_true : l34CQ = true := by
  unfold l34CQ l34C
  rw [hS.1, cent1, r1_eq]
  refine cqTab_of L34Scan.canonC.1 (fun c hc => ?_) (cnRP (by decide)) kCQ9304
  obtain ⟨h1, h2⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kInv9304 c hc)
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem l34Key_true : l34Key = true := by
  unfold l34Key l34C
  rw [hR.1, hS.1, cent1, r1_eq]
  refine keyTab_of pinR.canon L34Scan.canonC.1 (cnRP (by decide)) ?_
  exact scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
    have h1 := key9304All s hs
    unfold key9304 at h1
    rwa [strictB_app] at h1

end CertificateChecks.KernelLC.L34Key

end
