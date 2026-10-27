module

public import Certificates.Kernel.UnitarySix.Sec3.Gens
public import Certificates.Kernel.UnitarySix.Sec3.CA3
public import Certificates.Kernel.UnitarySix.Sec3.CA4
public import Certificates.Kernel.UnitarySix.Sec3.CX8
public import Certificates.Kernel.UnitarySix.Sec3.CSig
public import Certificates.Kernel.UnitarySix.Sec3.CLam
public import Certificates.Kernel.UnitarySix.Sec3.CZ2S
public import Certificates.Kernel.UnitarySix.Sec3.CX6Z
public import Certificates.Kernel.UnitarySix.Sec3.CZ
public import Certificates.Kernel.UnitarySix.Sec3.CX1Z
public import Certificates.Kernel.UnitarySix.Sec3.CP2
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

theorem chA3_K : ChainK chA3 16 2 CA3.BP 11 CA3.S CA3.SI CA3.LR CA3.TR CA3.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA3.head, CA3.hl, by norm_num, CA3.hs,
    by decide +kernel,
    O_of_wordGA chA3 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA4_K : ChainK chA4 5 2 CA4.BP 11 CA4.S CA4.SI CA4.LR CA4.TR CA4.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA4.head, CA4.hl, by norm_num, CA4.hs,
    by decide +kernel,
    O_of_wordGA chA4 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX8_K : ChainK chX8 2 1 CX8.BP 11 CX8.S CX8.SI CX8.LR CX8.TR CX8.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX8.head, CX8.hl, by norm_num, CX8.hs,
    by decide +kernel,
    O_of_wordGA chX8 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chSig_K : ChainK chSig 2 1 CSig.BP 11 CSig.S CSig.SI CSig.LR CSig.TR CSig.TRI :=
  ⟨by decide, by decide, by decide +kernel, CSig.head, CSig.hl, by norm_num, CSig.hs,
    by decide +kernel,
    O_of_wordGA chSig (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chLam_K : ChainK chLam 6 3 CLam.BP 11 CLam.S CLam.SI CLam.LR CLam.TR CLam.TRI :=
  ⟨by decide, by decide, by decide +kernel, CLam.head, CLam.hl, by norm_num, CLam.hs,
    by decide +kernel,
    O_of_wordGA chLam (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chZ2S_K : ChainK chZ2S 3 1 CZ2S.BP 11 CZ2S.S CZ2S.SI CZ2S.LR CZ2S.TR CZ2S.TRI :=
  ⟨by decide, by decide, by decide +kernel, CZ2S.head, CZ2S.hl, by norm_num, CZ2S.hs,
    by decide +kernel,
    O_of_wordGA chZ2S (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX6Z_K : ChainK chX6Z 5 1 CX6Z.BP 11 CX6Z.S CX6Z.SI CX6Z.LR CX6Z.TR CX6Z.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX6Z.head, CX6Z.hl, by norm_num, CX6Z.hs,
    by decide +kernel,
    O_of_wordGA chX6Z (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chZ_K : ChainK chZ 1 1 CZ.BP 11 CZ.S CZ.SI CZ.LR CZ.TR CZ.TRI :=
  ⟨by decide, by decide, by decide +kernel, CZ.head, CZ.hl, by norm_num, CZ.hs, by decide +kernel,
    O_of_wordGA chZ (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX1Z_K : ChainK chX1Z 5 1 CX1Z.BP 11 CX1Z.S CX1Z.SI CX1Z.LR CX1Z.TR CX1Z.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX1Z.head, CX1Z.hl, by norm_num, CX1Z.hs,
    by decide +kernel,
    O_of_wordGA chX1Z (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chP2_K : ChainK chP2 21 3 CP2.BP 11 CP2.S CP2.SI CP2.LR CP2.TR CP2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CP2.head, CP2.hl, by norm_num, CP2.hs,
    by decide +kernel,
    O_of_wordGA chP2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

end CertificateChecks.KernelU6.Sec3
