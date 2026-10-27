module

public import Certificates.Data.Kernel.F4InvComm

public section

namespace CFSG.KD.F4Inv

open CFSG.KC.F4Inv CFSG.KC.F4Syl3

theorem comm_t : allN 4 (fun i => commN (invT 0) (i + 4) == if i = 0 then 0 else 1) = true := by
  decide +kernel

theorem comm_tu :
    allN 4 (fun i => commN (invT 2) (i + 4) == if i = 0 ∨ i = 3 then 0 else 1) = true := by
  decide +kernel

end CFSG.KD.F4Inv

end
