module

public import Certificates.Kernel.TWLKF.D510
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLKF510

open Certificates.TWLK

theorem roots : kRootsOK 5 10 RF = true := by decide +kernel

theorem cover : kCover 10 S T = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

end CFSG.KD.TWLKF510

#kc_each CFSG.KD.TWLKF510 twf510s
  (Certificates.TWLKF.kPat1NAt 5 10 CFSG.KD.TWLKF510.RF CFSG.KD.TWLKF510.S) 0 20

#kc_each CFSG.KD.TWLKF510 twf510t
  (Certificates.TWLKF.kPat2NAt 5 10 CFSG.KD.TWLKF510.RF CFSG.KD.TWLKF510.T) 0 8

end
