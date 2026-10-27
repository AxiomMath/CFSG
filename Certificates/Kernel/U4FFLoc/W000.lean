module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_000 : LocValid1K false false false = true := by decide +kernel

theorem loc2_000 : LocValid2K false false false = true := by decide +kernel

theorem loc3_000 : LocValid3K false false false = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
