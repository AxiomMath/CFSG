module

public import Certificates.Data.SuzPairSize

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.RankThree.Native

@[expose] def pairGs : Array (Array Nat) := #[rebuild (levels ()) h1β, rebuild (levels ()) h2β]

@[expose] def keys : Array Nat := suzFiveKeys.toArray

end CertificateChecks.KernelSuzPump

end
