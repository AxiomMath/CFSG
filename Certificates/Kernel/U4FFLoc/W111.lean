module

public import Certificates.Data.Kernel.U4FFLocCheck

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_111 : LocValid1K true true true = true := by decide +kernel

theorem loc2_111 : LocValid2K true true true = true := by decide +kernel

theorem loc3_111 : LocValid3K true true true = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
