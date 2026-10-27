module

public import Certificates.Data.Kernel.U4FFLocCheck
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace Certificates.Kernel.U4FFLoc

open CFSG.KC.U4FFLoc

theorem loc1_011 : LocValid1K false true true = true := by decide +kernel

theorem loc2_011 : LocValid2K false true true = true := by decide +kernel

theorem loc3_011 : LocValid3K false true true = true := by decide +kernel

end Certificates.Kernel.U4FFLoc
