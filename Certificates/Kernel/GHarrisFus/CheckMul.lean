module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusCertInputs
public import Certificates.Data.Kernel.GHarrisFus.Tab
public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.Ring

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22609dm : dmOK dmT = true := by quickRfl
theorem ch22609mv : mvOK mvT = true := by quickRfl
theorem ch22609ct : ctOK CT (Array.toList SE.clsArr) = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
