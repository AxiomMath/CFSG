module

public import Certificates.Kernel.Sporadic.He.Chain2112
public import CFSG.Certificates.Kernel.Spor.PresCard
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem canonOK : allN 9 (fun j => bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HeC.S j),
    canonK 8330 14 (mask 14) (8330 * 14) (HeC.SI j))) = true := by
  quickRfl

theorem idOK : bAnd(canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14), idK 8330 14 (mask 14)) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.He2112

end
