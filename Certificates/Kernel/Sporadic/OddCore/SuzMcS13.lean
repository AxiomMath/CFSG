module

public import Certificates.Kernel.Sporadic.OddCore.CLogCmd
public import Certificates.Kernel.Sporadic.OddCore.SuzMcGlue
meta import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import Certificates.Kernel.Sporadic.OddCore.CLogGenZ
meta import Mathlib

public section

open CFSG.Sporadic.SuzRecog.MixedCell

#kclog CertificateChecks.KernelSpor.SuzMcS13 6 30 (baseRels ++ [cellRel 2 3]) [4, 6, 8] [0, 2]
  16383 30

namespace CertificateChecks.KernelSpor.SuzMcS13

theorem mem : collapseMem [cellRel 2 3] := SuzMc.collapse_of_log hd_0 hd_1 defs nf slices

end CertificateChecks.KernelSpor.SuzMcS13

end
