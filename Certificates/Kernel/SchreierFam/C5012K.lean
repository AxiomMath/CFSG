module

public import CFSG.GH74.E2.L33OuterTablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam

open CFSG.GH74.E2 CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

theorem conj_5012K : outerConjCheck L33.QP (elemsV L33.QA) = true := by decide +kernel

theorem comm_5012K : outerCommCheck L33.QP (elemsV L33.QA) (elemsV L33.QP) = true := by
  decide +kernel

end CertificateChecks.KernelSchreierFam
