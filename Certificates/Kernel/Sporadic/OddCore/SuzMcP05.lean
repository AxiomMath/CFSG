module

public import Certificates.Kernel.Sporadic.OddCore.CLogCmd
public import Certificates.Kernel.Sporadic.OddCore.SuzMcGlue
meta import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import Certificates.Kernel.Sporadic.OddCore.CLogGenZ
meta import Mathlib

public section

open CFSG.Sporadic.SuzRecog.MixedCell

#kclog CertificateChecks.KernelSpor.SuzMcP05 6 31 (baseRels ++ [cellRel 0 1, cellRel 2 8])
  [4, 6, 8] [0, 2] 16383 30

namespace CertificateChecks.KernelSpor.SuzMcP05

theorem mem : collapseMem [cellRel 0 1, cellRel 2 8] :=
  SuzMc.collapse_of_log hd_0 hd_1 defs nf slices

end CertificateChecks.KernelSpor.SuzMcP05

end
