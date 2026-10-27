module

public meta import Certificates.Kernel.PropA.Gen
public meta import Certificates.Kernel.PropA.PWords
public import Certificates.Kernel.PropA.Gen

public section

namespace CertificateChecks.KernelPropA.Gen

open CFSG.PSL3Four.Native CertificateChecks.KernelPropA

meta def gCKG1 : Array (Array Nat) := wts false pa450010wCKG
meta def giCKG1 : Array (Array Nat) := invs gCKG1
meta def gCKG2 : Array (Array Nat) := wts true pa450010wCKG
meta def giCKG2 : Array (Array Nat) := invs gCKG2
meta def dP : Array Nat := wt (gensK false) pa450010wd
meta def gPd : Array (Array Nat) := #[dP, invTab 28 dP]

end CertificateChecks.KernelPropA.Gen

end
