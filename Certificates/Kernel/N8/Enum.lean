module

public import Certificates.Data.Kernel.M24R.N8K
public import Certificates.Data.Kernel.CosetW.EnumW
public import CFSG.Certificates.PresentationLetters

public section

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200

open CFSG.CosetTable CFSG.CGT.M24R CFSG.Certificates.CosetEnumeration

namespace CFSG.KC.N8K

local notation "m6" => List.length (subsetOf 10 [0, 1, 2, 3, 4, 5])
local notation "m5" => List.length (subsetOf m6 [0, 1, 2, 3, 4])
local notation "m4" => List.length (subsetOf m5 [0, 1, 2, 3])
local notation "m3" => List.length (subsetOf m4 [0, 1, 2])
local notation "m2" => List.length (subsetOf m3 [0, 1])
local notation "m1" => List.length (subsetOf m2 [0])

theorem n8k_enumX : checkW (mkParamsW (2 * 10) (invArrW 10) (codes relsN8Ten)
    (codes ((subsetOf 10 [0, 1, 2, 3, 4, 5]).map fun x => [(x, true)]))) 1000 16 = true := by
  decide +kernel

theorem n8k_carm6 : checkW (mkParamsW (2 * m6) (invArrW m6) (codes carmR6)
    (codes ((subsetOf m6 [0, 1, 2, 3, 4]).map fun x => [(x, true)]))) 200 8 = true := by
  decide +kernel

theorem n8k_carm5 : checkW (mkParamsW (2 * m5) (invArrW m5) (codes carmR5)
    (codes ((subsetOf m5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 200 7 = true := by
  decide +kernel

theorem n8k_carm4 : checkW (mkParamsW (2 * m4) (invArrW m4) (codes carmR4)
    (codes ((subsetOf m4 [0, 1, 2]).map fun x => [(x, true)]))) 200 6 = true := by
  decide +kernel

theorem n8k_carm3 : checkW (mkParamsW (2 * m3) (invArrW m3) (codes carmR3)
    (codes ((subsetOf m3 [0, 1]).map fun x => [(x, true)]))) 200 5 = true := by
  decide +kernel

theorem n8k_carm2 : checkW (mkParamsW (2 * m2) (invArrW m2) (codes carmR2)
    (codes ((subsetOf m2 [0]).map fun x => [(x, true)]))) 200 4 = true := by
  decide +kernel

theorem n8k_carm1 : checkW (mkParamsW (2 * m1) (invArrW m1) (codes carmR1)
    (codes ((subsetOf m1 []).map fun x => [(x, true)]))) 200 3 = true := by
  decide +kernel

end CFSG.KC.N8K

end
