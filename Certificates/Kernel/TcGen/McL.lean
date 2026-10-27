module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelTc.McL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CertificateChecks.KernelTc.McL

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.McLThree

theorem tc_K : seedsL lay A B ⟨tcNregs, tcProg, tcSpec.facts⟩ tcSpec.rA tcSpec.rB = true := by
  quickRfl

theorem cp_K : seedsL lay A B ⟨cpNregs, cpProg, cpSpec.facts⟩ cpSpec.rA cpSpec.rB = true := by
  quickRfl

theorem tc_neg : (!seedsL lay B A ⟨tcNregs, tcProg, tcSpec.facts⟩ tcSpec.rA tcSpec.rB) = true := by
  quickRfl

theorem ne_neg : (!seedsL lay A B ⟨2, [], [.ne [(0, 1)] [(1, 1)] 21]⟩ 0 1) = true := by
  quickRfl

theorem exp_neg : (!seedsL lay A B ⟨2, [], [.eq [(0, 65536)] [(0, 65536)]]⟩ 0 1) = true := by
  quickRfl

end CertificateChecks.KernelTc.McL

end
