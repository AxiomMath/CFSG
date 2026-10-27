module

public import Certificates.Kernel.PhanB3.Tables
public import Certificates.Data.Kernel.Misc.Coset.Mem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelPhanB3

open CFSG.KC.MiscCoset

theorem walk0 : Mem.memOK CFSG.KBData.B3U.F 26132 [2, 2, 2] [4, 13603, 7] = true := by quickRfl

theorem walk1 : Mem.memOK CFSG.KBData.B3U.F 26132 [4, 4, 4, 4] [8, 70, 13396, 11] = true := by
  quickRfl

theorem walk2 : Mem.memOK CFSG.KBData.B3U.F 26132 [4, 0, 5, 1] [8, 13371, 23, 1] = true := by
  quickRfl

theorem walk3 : Mem.memOK CFSG.KBData.B3U.F 26132 [4, 1, 7, 0, 7] [8, 13376, 13413, 87, 13] =
    true := by
  quickRfl

theorem walk4 : Mem.memOK CFSG.KBData.B3U.F 26132 [4, 2, 5, 2, 1] [8, 66, 13391, 21, 1] = true := by
  quickRfl

theorem walk5 : Mem.memOK CFSG.KBData.B3U.F 26132 [6, 2, 7, 2, 6, 3] [12, 88, 13548, 271, 53, 5] =
    true := by
  quickRfl

end CertificateChecks.KernelPhanB3

end
