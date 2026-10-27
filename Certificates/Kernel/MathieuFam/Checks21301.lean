module

public import Certificates.Data.Kernel.Spor.Mathieu
public import CFSG.Holt.SmallGroupsCheck
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CertificateChecks.KernelMathieuFam

open CFSG.KS.Mathieu CFSG.Holt.SmallGroups

theorem m11Data4K : mcheck 11 4 m11Data4 = true := by quickRfl

end CertificateChecks.KernelMathieuFam

end
