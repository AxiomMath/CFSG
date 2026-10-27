module

public import CFSG.GH74.AS16.E2.Local3ChecksInputs
public import CFSG.GH74.KGroups.M11TablesInputs
public import CFSG.GH74.KGroups.L33TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.GH74.AS16.E2

theorem m11_local3_5000K : local3Check (elemsV M11.Q) M11.t0 = true := by
  decide +kernel

theorem m11_exp_5000K : expCheck (elemsV M11.Q) 27 3 = true := by
  decide +kernel

theorem l33_local3_5000K : local3Check (elemsV L33.QP) L33.t0 = true := by
  decide +kernel

theorem l33_exp_5000K : expCheck (elemsV L33.QP) 27 3 = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
