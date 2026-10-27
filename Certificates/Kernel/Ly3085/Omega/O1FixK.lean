module

import Certificates.Kernel.Ly3085.Omega.O1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyO1

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1fTA (fun b c => Nat.beq (CFSG.KC.LyOm.cFix BC KX PT TA n b 1) c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_fix_TA.txt.gz" 1726 3300370825710304508 186 306

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1fTB (fun b c => Nat.beq (CFSG.KC.LyOm.cFix BC KX PT TB n b 1) c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_fix_TB.txt.gz" 1726 8392712222508363423 0 306

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1fTT (fun b c => Nat.beq (CFSG.KC.LyOm.cFix BC KX PT TT n b 1) c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_fix_TT.txt.gz" 1726 6737125018369606007 0 306

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1fYB (fun b c => Nat.beq (CFSG.KC.LyOm.cFix BC KX PT YB n b 1) c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_fix_YB.txt.gz" 1726 3124073824352165980 0 306

end CFSG.KD.LyO1
