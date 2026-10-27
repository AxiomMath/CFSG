module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.LocalComp.J3Seeds
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3Cover

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

@[expose] def relPs (ws : List (List (Fin 3 × Bool))) :
    List (List (Fin 3 × Bool) × List (Fin 2 × Bool)) :=
  ws.map fun w => (w, [])

theorem chk : grpK 80 SA.M SB.M 2 3 (genWords.map natW)
    ((relPs checkWords).map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

end CertificateChecks.KernelJ3Cover

end
