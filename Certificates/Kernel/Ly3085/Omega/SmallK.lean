module

import Certificates.Kernel.Ly3085.Omega.SwData
public import Certificates.Kernel.Ly3085.Omega.HData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.LyS4

#kc_each CFSG.KD.LyS4 s4 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 0 122

#kc_repo #kc_each_rows CFSG.KD.LyS4 s4s (fun _ k₀ c => CFSG.KC.LyOm.sSort KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/s4_sort.txt.gz" 21 11326411699070542524 0 2

end CFSG.KD.LyS4

namespace CFSG.KD.LyH2

#kc_each CFSG.KD.LyH2 h2 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 0 95

#kc_repo #kc_each_rows CFSG.KD.LyH2 h2s (fun _ k₀ c => CFSG.KC.LyOm.sSort KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/h2_sort.txt.gz" 21 17693014752771632061 0 2

#kc_each CFSG.KD.LyH2 h2c (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1) 0 95

theorem h2cs : Nat.beq (CFSG.KC.LyOm.sCountSum CT nl) 44040255 = true := by quickRfl

end CFSG.KD.LyH2

namespace CFSG.KD.LyH3

#kc_each CFSG.KD.LyH3 h3 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 0 45

#kc_repo #kc_each_rows CFSG.KD.LyH3 h3s (fun _ k₀ c => CFSG.KC.LyOm.sSort KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/h3_sort.txt.gz" 9 11684268865402929654 0 1

#kc_each CFSG.KD.LyH3 h3c (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1) 0 45

theorem h3cs : Nat.beq (CFSG.KC.LyOm.sCountSum CT nl) 11010259 = true := by quickRfl

end CFSG.KD.LyH3

namespace CFSG.KD.LyH4

#kc_each CFSG.KD.LyH4 h4 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 0 16

#kc_repo #kc_each_rows CFSG.KD.LyH4 h4s (fun _ k₀ c => CFSG.KC.LyOm.sSort KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/h4_sort.txt.gz" 9 10214261938396630368 0 1

#kc_each CFSG.KD.LyH4 h4c (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1) 0 16

theorem h4cs : Nat.beq (CFSG.KC.LyOm.sCountSum CT nl) 11010153 = true := by quickRfl

end CFSG.KD.LyH4

end
