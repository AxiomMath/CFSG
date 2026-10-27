module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_001 : LocValid1K false false true = true := by decide +kernel

theorem loc2_001 : LocValid2K false false true = true := by decide +kernel

theorem loc3_001 : LocValid3K false false true = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
