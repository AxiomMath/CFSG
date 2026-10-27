
module

public import Certificates.Kernel.Misc.Perm.J2C3A
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Misc.SetCodes

theorem setsK_repeated_neg : (!setsK 315 2 15 9 (fun _ => O6 0)) = true := by quickRfl

theorem actsK_shift_neg : (!actsK 6 15 9 O6 Z (fun i => (i + 1) % 6)) = true := by quickRfl

theorem fixesK_z : fixesK 6 15 9 O6 Z = true := by quickRfl

end CertificateChecks.KernelMisc.J2C3

end
