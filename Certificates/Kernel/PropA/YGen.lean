module

public meta import Certificates.Kernel.PropA.FactGen
public meta import Certificates.Kernel.PropA.YWords
public import Certificates.Kernel.PropA.Gen

public section

namespace CertificateChecks.KernelPropA.Gen

open CertificateChecks.KernelPropA

meta def gXR : Array (Array Nat) := wts false pa450010wXR
meta def giXR : Array (Array Nat) := invs gXR
meta def tXR : Array (Array Nat) := enumT false gXR giXR idT 2
meta def gTX1 : Array (Array Nat) := wts false pa450010wTX
meta def giTX1 : Array (Array Nat) := invs gTX1
meta def gTX2 : Array (Array Nat) := wts true pa450010wTX
meta def giTX2 : Array (Array Nat) := invs gTX2
meta def tTX1 : Array (Array Nat) := enumT false gTX1 giTX1 idT 4
meta def tTX2 : Array (Array Nat) := enumT false gTX2 giTX2 idT 4
meta def tCDU : Array (Array Nat) := enumT false gCDU giCDU idT 36
meta def qU : Array (Array Nat) := #[ru]

end CertificateChecks.KernelPropA.Gen

end
