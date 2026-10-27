module

public import Certificates.Data.Kernel.TabMatGrp
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import Certificates.Data.CFSGNative.J3.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3Cover.Model

open CFSG.KC.TabMatGrp
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

@[expose] def MA : Nat :=
  16554017676901069058611951203757408810937110361883683190471399831476936674513590924997047577214985

@[expose] def MB : Nat :=
  26378808950576977522132585510111478991421399333323025063402770214161311448327943718807329510523077

@[expose] def modelPs : List (List (Fin 3 × Bool) × List (Fin 2 × Bool)) :=
  (cover ++ [walkWord ++ walkWord ++ walkWord]).map fun w => (w, [])

theorem chk : grpK 18 MA MB 2 3 (genWords.map natW)
    (modelPs.map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

theorem dist : distK 18 MA MB 2 3 (genWords.map natW) ([walkWord, []].map natW) = true := by
  quickRfl

end CertificateChecks.KernelJ3Cover.Model

end
