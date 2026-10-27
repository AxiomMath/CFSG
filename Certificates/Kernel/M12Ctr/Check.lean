module

public import Certificates.Data.Kernel.M12Ctr

public section

set_option maxRecDepth 400000

namespace Certificates.KernelM12Ctr

open Certificates.KernelM12Ctr

theorem kOrb : orbOK = true := by decide +kernel

theorem kCent : centOK = true := by decide +kernel

theorem kTup : tupOK = true := by decide +kernel

end Certificates.KernelM12Ctr

end
