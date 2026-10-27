module

public import Certificates.Kernel.Sporadic.OddCore.CLogCmd
public import Certificates.Kernel.Sporadic.OddCore.SuzMcGlue
meta import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import Certificates.Kernel.Sporadic.OddCore.CLogGenZ
meta import Mathlib

public section

open CFSG.Sporadic.SuzRecog.MixedCell

#kclog CertificateChecks.KernelSpor.SuzMcP06 6 31 (baseRels ++ [cellRel 0 8, cellRel 2 0])
  [4, 6, 8] [0, 2] 16383 30

namespace CertificateChecks.KernelSpor.SuzMcP06

theorem mem : collapseMem [cellRel 0 8, cellRel 2 0] :=
  SuzMc.collapse_of_log hd_0 hd_1 defs nf slices

end CertificateChecks.KernelSpor.SuzMcP06

end
