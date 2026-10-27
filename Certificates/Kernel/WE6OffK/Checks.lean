module

public import Certificates.Data.Kernel.WE6OffK
public import Certificates.Data.WE6Offender
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelWE6Off

open CFSG.KC.WE6K Certificates.WE6Offender

theorem base : baseOK LCode = true := by quickRfl

theorem ord : rngK 0 81 (ordRow LCode ordMask) = true := by quickRfl

theorem comm0 : rngK 0 27 (commRow LCode commMasks) = true := by quickRfl
theorem comm1 : rngK 27 27 (commRow LCode commMasks) = true := by quickRfl
theorem comm2 : rngK 54 27 (commRow LCode commMasks) = true := by quickRfl

theorem fix0 : rngK 0 27 (fixRow LCode fixCodes) = true := by quickRfl
theorem fix1 : rngK 27 27 (fixRow LCode fixCodes) = true := by quickRfl
theorem fix2 : rngK 54 27 (fixRow LCode fixCodes) = true := by quickRfl

theorem bound0 : rngK 0 27 (boundRow LCode commMasks fixCodes ordMask) = true := by quickRfl
theorem bound1 : rngK 27 27 (boundRow LCode commMasks fixCodes ordMask) = true := by quickRfl
theorem bound2 : rngK 54 27 (boundRow LCode commMasks fixCodes ordMask) = true := by quickRfl

end CertificateChecks.KernelWE6Off
