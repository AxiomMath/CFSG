module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Chain3850Data
meta import Certificates.Kernel.OmegaEight.Chain3850Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import Mathlib
meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
meta import Mathlib

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelO8.Chain3850.CP 64 7 64
  CertificateChecks.KernelO8.Chain3850.strongP CertificateChecks.KernelO8.Chain3850.baseP 7
  CFSG.EvenSmallLie.OmegaEight.NSplit.extraWordsPlus

#ks_rawchain CertificateChecks.KernelO8.Chain3850.CM 64 7 64
  CertificateChecks.KernelO8.Chain3850.strongM CertificateChecks.KernelO8.Chain3850.baseM 7
  CFSG.EvenSmallLie.OmegaEight.NSplit.extraWordsMinus

namespace CertificateChecks.KernelO8.Chain3850

open CFSG.KS CFSG.KC.Enum

theorem permP : CFSG.KC.Enum.allN 16 (fun j => permOK 64 7 (mask 7) (64 * 7) (CP.S j) (CP.SI j)) =
    true := by
  quickRfl

theorem permM : CFSG.KC.Enum.allN 14 (fun j => permOK 64 7 (mask 7) (64 * 7) (CM.S j) (CM.SI j)) =
    true := by
  quickRfl

end CertificateChecks.KernelO8.Chain3850

end
