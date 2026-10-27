module

public import Certificates.Data.Kernel.PermCent.Moore7C

public section

namespace Certificates.Kernel.Moore7

open CFSG.Certificates.Kernel.PkCV

theorem m7F_true : m7F = true := by
  decide +kernel

end Certificates.Kernel.Moore7

end
