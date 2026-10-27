module

public import Certificates.Data.SuzPump

public section

namespace CertificateChecks.KernelSuzPump

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.RankThree.Native

@[expose] def pumpGs : Array (Array Nat) := #[rebuild (levels ()) g1β, rebuild (levels ()) g2β]

@[expose] def yGs : Array (Array Nat) := #[rebuild (levels ()) uβ, rebuild (levels ()) vβ]

@[expose] def fuseRows : Array (Array Nat) := fuseTab ()

@[expose] def fuseTs : Array (Array Nat) := (fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7)

@[expose] def fuseNs : Array (Array Nat) :=
  (fuseTab ()).map fun r => rebuild (levels ()) (r.extract 7 13)

end CertificateChecks.KernelSuzPump

end
