module

public import Certificates.Data.Kernel.T75M23.L2K7G
public import Certificates.Kernel.CosPresTab.M23Tab
public import Certificates.Kernel.T75M23.L2K7FData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.KC.TabWord.M23 (NL)
open CFSG.KD.T75M23L2F (s2 s3 reps cw swr kc kw)

theorem swPass_ok : swPassK NL s2 s3 = true := by quickRfl

theorem swConj_ok : swConjK NL s2 reps cw = true := by quickRfl

theorem swRows_ok : swRowsK NL s2 s3 reps swr = true := by quickRfl

theorem klK7_ok : klK7 NL kc kw = true := by quickRfl

end CFSG.KC.N7K

end
