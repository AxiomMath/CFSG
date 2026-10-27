module

public import Certificates.Kernel.TWLKF.D77
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLKF77

open Certificates.TWLK

theorem roots : kRootsOK 7 7 RF = true := by decide +kernel

theorem cover : kCover 7 S T = true := by decide +kernel

theorem lenS : S.length = 16 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

end CFSG.KD.TWLKF77

#kc_each CFSG.KD.TWLKF77 twf77s
  (Certificates.TWLKF.kPat1NAt 7 7 CFSG.KD.TWLKF77.RF CFSG.KD.TWLKF77.S) 0 16

#kc_each CFSG.KD.TWLKF77 twf77t
  (Certificates.TWLKF.kPat2NAt 7 7 CFSG.KD.TWLKF77.RF CFSG.KD.TWLKF77.T) 0 8

end
