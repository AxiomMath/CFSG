module

public import Certificates.Kernel.TwoHS.HarCKP
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum

theorem rlE_lo : allN 4 (fun r => rlE r 0) = true := by
  quickRfl

theorem rlE40 : rlE 4 0 = true := by
  quickRfl

theorem rlE50 : rlE 5 0 = true := by
  quickRfl

theorem rlE51 : rlE 5 1 = true := by
  quickRfl

theorem rlE60 : rlE 6 0 = true := by
  quickRfl

theorem rlE61 : rlE 6 1 = true := by
  quickRfl

theorem rlE70 : rlE 7 0 = true := by
  quickRfl

theorem rlE71 : rlE 7 1 = true := by
  quickRfl

theorem rlE80 : rlE 8 0 = true := by
  quickRfl

theorem rlE81 : rlE 8 1 = true := by
  quickRfl

theorem rlE90 : rlE 9 0 = true := by
  quickRfl

theorem rlE91 : rlE 9 1 = true := by
  quickRfl

theorem rlE92 : rlE 9 2 = true := by
  quickRfl

theorem mbE_ok : mbE = true := by
  quickRfl

end CFSG.KD.TwoHS

end

#kc_each CFSG.KD.TwoHS.clPE 0 6
