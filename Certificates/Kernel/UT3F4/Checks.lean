module

public import Certificates.Data.Kernel.UT3F4.Check

public section

namespace Certificates.Kernel.UT3F4

open CFSG.Certificates.Kernel.UT3F4

theorem checkN_true : checkN = true := by decide +kernel

end Certificates.Kernel.UT3F4

end
