module

public import Certificates.Kernel.Sporadic.OddCore.CLogCmd
public import Certificates.Kernel.Sporadic.OddCore.SuzMcGlue
meta import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import Certificates.Kernel.Sporadic.OddCore.CLogGenZ
meta import Mathlib

public section

open CFSG.Sporadic.SuzRecog.MixedCell

#kclog CertificateChecks.KernelSpor.SuzMcS00 6 30 (baseRels ++ [cellRel 0 2]) [4, 6, 8] [0, 2]
  16383 30

namespace CertificateChecks.KernelSpor.SuzMcS00

theorem mem : collapseMem [cellRel 0 2] := SuzMc.collapse_of_log hd_0 hd_1 defs nf slices

theorem negZ : Bool.not (CFSG.KC.CLog.hdK 6 30 (CFSG.KS.PEnum.r32 N 0) (CFSG.KS.PEnum.r32 N 2) 336
    10 (baseRels ++ [cellRel 0 2]) [4, 6, 8] RL (CFSG.KS.PEnum.r32 RN) FD) = true := by
  quickRfl

theorem negRel : Bool.not (CFSG.KC.CLog.hdK 6 30 (CFSG.KS.PEnum.r32 N 0) (CFSG.KS.PEnum.r32 N 2)
    336 0 (baseRels ++ [cellRel 0 2 ++ [0]]) [4, 6, 8] RL (CFSG.KS.PEnum.r32 RN) FD) = true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzMcS00

end
