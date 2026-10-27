module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_110 : LocValid1K true true false = true := by decide +kernel

theorem loc2_110 : LocValid2K true true false = true := by decide +kernel

theorem loc3_110 : LocValid3K true true false = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
