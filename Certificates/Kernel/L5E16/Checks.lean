module

public import Certificates.Data.Kernel.L5E16.Defs
public import Certificates.Kernel.L5E16.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL5E16

open CFSG.KC.L5E16 CFSG.KD.L5E16

@[expose] def oneK : Nat := 583706118939841765935136

theorem ch5058_closed : closedK oneK S G = true := by quickRfl

theorem ch5058_e16 : e16K oneK S R = true := by quickRfl

end CertificateChecks.KernelL5E16

end
