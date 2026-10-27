module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.GH74.KGroups.L33Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.CGT.PushingUpLit.SolKNA.R4.Check

theorem q16_9753K : noQ16Check (elemsV L33.QA) (pickReps (elemsV L33.QA)) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
