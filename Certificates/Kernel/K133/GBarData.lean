module

public import Certificates.Kernel.LocalComp.BfsGenKey
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartOne.K133Spor.GBarInputs
public meta import CFSG.RankThree.PartOne.K133Spor.GBarInputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.HNOddCore.QCheckInputs

namespace CertificateChecks.KernelK133.GBarE

public meta def gens : List (Array Nat) := CFSG.Sporadic.HNOddCore.Native.colPerms.toList

end CertificateChecks.KernelK133.GBarE

public section

set_option maxRecDepth 400000

#lc_bfs_key CertificateChecks.KernelK133.GB CertificateChecks.KernelK133.GBarE.gens
  CFSG.RankThree.PartOne.K133Spor.gbarKeys 256 9 400

end
