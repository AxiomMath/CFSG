module

public import Certificates.Kernel.UnitarySix.Sec3.Gens
public import Certificates.Kernel.UnitarySix.Sec3.CX3A3
public import Certificates.Kernel.UnitarySix.Sec3.CSigA3
public import CFSG.Certificates.Kernel.U6Sec3ElemSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.U6Sec3.SEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KC.Enum
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem chX3A3_K : ChainK chX3A3 18 3 CX3A3.BP 11 CX3A3.S CX3A3.SI CX3A3.LR CX3A3.TR CX3A3.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX3A3.head, CX3A3.hl, by norm_num, CX3A3.hs,
    by decide +kernel,
    O_of_wordGA chX3A3 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chSigA3_K :
    ChainK chSigA3 20 3 CSigA3.BP 11 CSigA3.S CSigA3.SI CSigA3.LR CSigA3.TR CSigA3.TRI :=
  ⟨by decide, by decide, by decide +kernel, CSigA3.head, CSigA3.hl, by norm_num, CSigA3.hs,
    by decide +kernel,
    O_of_wordGA chSigA3 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

end CertificateChecks.KernelU6.Sec3
