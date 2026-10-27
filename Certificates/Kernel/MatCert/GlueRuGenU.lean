module

public import Certificates.Kernel.MatCert.Glue
public import Certificates.Kernel.MatCert.RuGenU

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Blueprint
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem ruGenU :
    MGenU.check (ops2 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 ru_7_genu = true := by
  rw [MGenU.check, ru7genu_wf,
    mcertCheck_of_N (hom2 28 (by norm_num)) ruA ruB trivial trivial ru7genu_K]
  rfl

end CertificateChecks.KernelMC

end
