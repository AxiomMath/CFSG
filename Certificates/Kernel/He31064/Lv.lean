module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CL

open CFSG.KC.DcTup CFSG.KD.He31064

theorem pow : allL (powOK 8330) lv = true := by quickRfl
theorem w0 : tabOK rg (nthL lvw 0) 8330 (nth (nthL lv 0) 1) = true := by quickRfl
theorem w1 : tabOK rg (nthL lvw 1) 8330 (nth (nthL lv 1) 1) = true := by quickRfl
theorem w2 : tabOK rg (nthL lvw 2) 8330 (nth (nthL lv 2) 1) = true := by quickRfl
theorem w3 : tabOK rg (nthL lvw 3) 8330 (nth (nthL lv 3) 1) = true := by quickRfl
theorem w4 : tabOK rg (nthL lvw 4) 8330 (nth (nthL lv 4) 1) = true := by quickRfl
theorem w5 : tabOK rg (nthL lvw 5) 8330 (nth (nthL lv 5) 1) = true := by quickRfl

end CFSG.KD.He31064.CL

end
