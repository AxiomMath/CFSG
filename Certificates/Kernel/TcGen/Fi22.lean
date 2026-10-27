module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22ThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelTc.Fi22 3 77
  CFSG.Blueprint.NativeSporadic.Fi22Seed1 CFSG.Blueprint.NativeSporadic.Fi22Seed2

public section

namespace CertificateChecks.KernelTc.Fi22

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi22Three

theorem tc_K : seedsL lay A B ⟨tcNregs, tcProg, tcSpec.facts⟩ tcSpec.rA tcSpec.rB = true := by
  quickRfl

theorem cp_K : seedsL lay A B ⟨cpNregs, cpProg, cpSpec.facts⟩ cpSpec.rA cpSpec.rB = true := by
  quickRfl

theorem seed_neg : (!seedsL lay A B ⟨2, [], []⟩ 1 0) = true := by
  quickRfl

end CertificateChecks.KernelTc.Fi22

end
