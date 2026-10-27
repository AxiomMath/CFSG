module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelTc.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

public section

namespace CertificateChecks.KernelTc.ON

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.ONThree

theorem tc_K : seedsL lay A B ⟨tcNregs, tcProg, tcSpec.facts⟩ tcSpec.rA tcSpec.rB = true := by
  quickRfl

theorem cp_K : seedsL lay A B ⟨cpNregs, cpProg, cpSpec.facts⟩ cpSpec.rA cpSpec.rB = true := by
  quickRfl

theorem eq_neg : (!seedsL lay A B ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩ 0 1) = true := by
  quickRfl

end CertificateChecks.KernelTc.ON

end
