module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_100 : LocValid1K true false false = true := by decide +kernel

theorem loc2_100 : LocValid2K true false false = true := by decide +kernel

theorem loc3_100 : LocValid3K true false false = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
