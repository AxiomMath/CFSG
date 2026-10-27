module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_010 : LocValid1K false true false = true := by decide +kernel

theorem loc2_010 : LocValid2K false true false = true := by decide +kernel

theorem loc3_010 : LocValid3K false true false = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
