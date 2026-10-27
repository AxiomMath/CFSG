module

public import Certificates.Kernel.UnitarySix.Sec3.Gens
public import Certificates.Kernel.UnitarySix.Sec3.CA2s0
public import Certificates.Kernel.UnitarySix.Sec3.CA2s1
public import Certificates.Kernel.UnitarySix.Sec3.CA2s2
public import Certificates.Kernel.UnitarySix.Sec3.CA1s0
public import Certificates.Kernel.UnitarySix.Sec3.CA1s1
public import Certificates.Kernel.UnitarySix.Sec3.CA3s0
public import Certificates.Kernel.UnitarySix.Sec3.CA3s1
public import Certificates.Kernel.UnitarySix.Sec3.CA3s2
public import Certificates.Kernel.UnitarySix.Sec3.CA3s3
public import Certificates.Kernel.UnitarySix.Sec3.CA3s4
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

theorem chA2s0_K : ChainK chA2s0 9 3 CA2s0.BP 11 CA2s0.S CA2s0.SI CA2s0.LR CA2s0.TR CA2s0.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA2s0.head, CA2s0.hl, by norm_num, CA2s0.hs,
    by decide +kernel,
    O_of_wordGA chA2s0 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA2s1_K : ChainK chA2s1 11 3 CA2s1.BP 11 CA2s1.S CA2s1.SI CA2s1.LR CA2s1.TR CA2s1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA2s1.head, CA2s1.hl, by norm_num, CA2s1.hs,
    by decide +kernel,
    O_of_wordGA chA2s1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA2s2_K : ChainK chA2s2 13 3 CA2s2.BP 11 CA2s2.S CA2s2.SI CA2s2.LR CA2s2.TR CA2s2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA2s2.head, CA2s2.hl, by norm_num, CA2s2.hs,
    by decide +kernel,
    O_of_wordGA chA2s2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA1s0_K : ChainK chA1s0 9 1 CA1s0.BP 11 CA1s0.S CA1s0.SI CA1s0.LR CA1s0.TR CA1s0.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA1s0.head, CA1s0.hl, by norm_num, CA1s0.hs,
    by decide +kernel,
    O_of_wordGA chA1s0 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA1s1_K : ChainK chA1s1 9 1 CA1s1.BP 11 CA1s1.S CA1s1.SI CA1s1.LR CA1s1.TR CA1s1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA1s1.head, CA1s1.hl, by norm_num, CA1s1.hs,
    by decide +kernel,
    O_of_wordGA chA1s1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA3s0_K : ChainK chA3s0 14 2 CA3s0.BP 11 CA3s0.S CA3s0.SI CA3s0.LR CA3s0.TR CA3s0.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3s0.head, CA3s0.hl, by norm_num, CA3s0.hs,
    by decide +kernel,
    O_of_wordGA chA3s0 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA3s1_K : ChainK chA3s1 13 2 CA3s1.BP 11 CA3s1.S CA3s1.SI CA3s1.LR CA3s1.TR CA3s1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3s1.head, CA3s1.hl, by norm_num, CA3s1.hs,
    by decide +kernel,
    O_of_wordGA chA3s1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA3s2_K : ChainK chA3s2 17 2 CA3s2.BP 11 CA3s2.S CA3s2.SI CA3s2.LR CA3s2.TR CA3s2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3s2.head, CA3s2.hl, by norm_num, CA3s2.hs,
    by decide +kernel,
    O_of_wordGA chA3s2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA3s3_K : ChainK chA3s3 17 2 CA3s3.BP 11 CA3s3.S CA3s3.SI CA3s3.LR CA3s3.TR CA3s3.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3s3.head, CA3s3.hl, by norm_num, CA3s3.hs,
    by decide +kernel,
    O_of_wordGA chA3s3 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA3s4_K : ChainK chA3s4 17 2 CA3s4.BP 11 CA3s4.S CA3s4.SI CA3s4.LR CA3s4.TR CA3s4.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3s4.head, CA3s4.hl, by norm_num, CA3s4.hs,
    by decide +kernel,
    O_of_wordGA chA3s4 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

end CertificateChecks.KernelU6.Sec3
