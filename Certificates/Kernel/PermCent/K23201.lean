module

public import Certificates.Data.Kernel.PermCent.L216Syl

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L216S.K23201

open CFSG.GH74.Uniqueness.SU.K.R4.L216M

theorem kSift : siftC QP (sC * sC) 0 = false := by decide +kernel

theorem kComm : eq22C sC (cOf pa) (cOf pa) sC = true := by decide +kernel

theorem kLen : elT.length = 64 := by decide +kernel

theorem kNodup : nodupC elT = true := by decide +kernel

theorem kStable : stableC elT = true := by decide +kernel

theorem kCov : covC elT conjC = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L216S.K23201

end
