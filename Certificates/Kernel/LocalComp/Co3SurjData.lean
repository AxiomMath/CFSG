module

public import Certificates.Kernel.LocalComp.SurjGen
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Data.Kernel.SurjK
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentBridgeInputs
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentBridgeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.Co3Surj.SA CFSG.Sporadic.Co3.Native.seedA
#ks_chars CertificateChecks.KernelLC.Co3Surj.SB CFSG.Sporadic.Co3.Native.seedB
#ks_chars CertificateChecks.KernelLC.Co3Surj.IT CFSG.Sporadic.Bridge.SurjD.Native.co3ImgText
#ks_chars CertificateChecks.KernelLC.Co3Surj.ST CFSG.Sporadic.Bridge.SurjD.Native.co3SurjText
#lc_words CertificateChecks.KernelLC.Co3Surj.IW CFSG.Sporadic.Bridge.SurjD.Native.co3ImgText
#lc_words CertificateChecks.KernelLC.Co3Surj.SW CFSG.Sporadic.Bridge.SurjD.Native.co3SurjText
#lc_surj CertificateChecks.KernelLC.Co3Surj.CS CFSG.Sporadic.Co3.Native.co3Data
  CFSG.EvenSmallLie.SympSix.Co3Ident.vImgWords

namespace CertificateChecks.KernelLC.Co3Surj

open CFSG.KC.SurjK CFSG.KC.M1F2

@[expose] noncomputable def orbF (k : Nat) : Bool :=
  orbStep 22 11178 CS.A CS.B 1 CS.PT CS.PA CS.LB CS.AP CS.BP CS.SO CS.SOI k

end CertificateChecks.KernelLC.Co3Surj

#lc_blocks CertificateChecks.KernelLC.Co3Surj.BO CertificateChecks.KernelLC.Co3Surj.orbF 11178 1024

end
