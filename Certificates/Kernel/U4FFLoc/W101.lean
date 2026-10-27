module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_101 : LocValid1K true false true = true := by decide +kernel

theorem loc2_101 : LocValid2K true false true = true := by decide +kernel

theorem loc3_101 : LocValid3K true false true = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
