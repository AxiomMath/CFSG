module

public import Certificates.Kernel.Tc.RuK
public import Certificates.Kernel.Tc.RuJTab
public import Certificates.Data.Kernel.HeLoc.PTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CertificateChecks.KernelSporSch
  CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

@[expose] noncomputable def fr (i : Nat) : Nat := nIf(Nat.beq i 1, 2, nIf(Nat.beq i 2, 10, 0))

theorem kTail : ptK 4060 12 18 RuJT.NR RuJT.NR RuJT.LT RuJT.PT RuJT.QT RuJO.LR fr ruRels (t3 0)
    bs ruKeys kc TC.SK 2160 4 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by quickRfl

end CertificateChecks.KernelTc.Ru

end
