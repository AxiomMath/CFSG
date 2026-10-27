module

public import Certificates.Kernel.Sporadic.Fi22.FivePin
public import Certificates.Kernel.Sporadic.Fi22.D4Data
public import Certificates.Kernel.OmegaEight.Chains3009
public import Certificates.Data.Kernel.Fi22.D4Set
public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Data.Fi22FiveD4
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22D4

open CFSG.KC.Enum CFSG.KC.Fi22D4 CFSG.KC.PermWit CertificateChecks.KernelSpor
open CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4

@[expose] noncomputable def d4K : Bool :=
  ltL ordList 4096 &&
  strictB (packL ordList) fun O =>
    bijK O (Fi22D4T 0) &&
    allN 6 (fun j => presK O (Fi22D4T 0) (Fi22Pin.pin j)) &&
    outK O (Fi22D4T 0) (Fi22W.W [1]) &&
    resK O (Fi22D4T 1) (Fi22Pin.pin 6) && resK O (Fi22D4T 2) (Fi22Pin.pin 7) &&
    siftR 360 9 KernelO8.AQ.LR KernelO8.AQ.TRI KernelO8.AQ.BP 7 (Fi22D4T 1) &&
    siftR 360 9 KernelO8.AQ.LR KernelO8.AQ.TRI KernelO8.AQ.BP 7 (Fi22D4T 2) &&
    faithK O (Fi22Pin.pin 0) (Fi22Pin.pin 1)

theorem ok : d4K = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22D4

end
