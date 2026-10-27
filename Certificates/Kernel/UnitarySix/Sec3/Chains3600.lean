module

public import Certificates.Kernel.UnitarySix.Sec3.Gens
public import Certificates.Kernel.UnitarySix.Sec3.CS
public import Certificates.Kernel.UnitarySix.Sec3.CX1
public import Certificates.Kernel.UnitarySix.Sec3.CX2
public import Certificates.Kernel.UnitarySix.Sec3.CX3
public import Certificates.Kernel.UnitarySix.Sec3.CK1
public import Certificates.Kernel.UnitarySix.Sec3.CK2
public import Certificates.Kernel.UnitarySix.Sec3.CA1
public import Certificates.Kernel.UnitarySix.Sec3.CA2
public import Certificates.Kernel.UnitarySix.Sec3.CK1A1
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2
public import Certificates.Kernel.UnitarySix.Sec3.CL
public import Certificates.Kernel.UnitarySix.Sec3.CB12
public import Certificates.Kernel.UnitarySix.Sec3.CB23
public import Certificates.Kernel.UnitarySix.Sec3.CSJ
public import Certificates.Kernel.UnitarySix.Sec3.CT1
public import Certificates.Kernel.UnitarySix.Sec3.CT2
public import CFSG.Certificates.Kernel.U6Sec3ElemSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.U6Sec3.SEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KC.Enum
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem chS_K : ChainK chS 5 3 CS.BP 11 CS.S CS.SI CS.LR CS.TR CS.TRI :=
  ⟨by decide, by decide, by decide +kernel, CS.head, CS.hl, by norm_num, CS.hs, by decide +kernel,
    O_of_wordGA chS (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX1_K : ChainK chX1 2 1 CX1.BP 11 CX1.S CX1.SI CX1.LR CX1.TR CX1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX1.head, CX1.hl, by norm_num, CX1.hs,
    by decide +kernel,
    O_of_wordGA chX1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX2_K : ChainK chX2 2 1 CX2.BP 11 CX2.S CX2.SI CX2.LR CX2.TR CX2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX2.head, CX2.hl, by norm_num, CX2.hs,
    by decide +kernel,
    O_of_wordGA chX2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chX3_K : ChainK chX3 1 1 CX3.BP 11 CX3.S CX3.SI CX3.LR CX3.TR CX3.TRI :=
  ⟨by decide, by decide, by decide +kernel, CX3.head, CX3.hl, by norm_num, CX3.hs,
    by decide +kernel,
    O_of_wordGA chX3 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chK1_K : ChainK chK1 9 3 CK1.BP 11 CK1.S CK1.SI CK1.LR CK1.TR CK1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CK1.head, CK1.hl, by norm_num, CK1.hs,
    by decide +kernel,
    O_of_wordGA chK1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chK2_K : ChainK chK2 9 3 CK2.BP 11 CK2.S CK2.SI CK2.LR CK2.TR CK2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CK2.head, CK2.hl, by norm_num, CK2.hs,
    by decide +kernel,
    O_of_wordGA chK2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA1_K : ChainK chA1 9 1 CA1.BP 11 CA1.S CA1.SI CA1.LR CA1.TR CA1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA1.head, CA1.hl, by norm_num, CA1.hs,
    by decide +kernel,
    O_of_wordGA chA1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chA2_K : ChainK chA2 12 3 CA2.BP 11 CA2.S CA2.SI CA2.LR CA2.TR CA2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CA2.head, CA2.hl, by norm_num, CA2.hs,
    by decide +kernel,
    O_of_wordGA chA2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chK1A1_K : ChainK chK1A1 22 4 CK1A1.BP 11 CK1A1.S CK1A1.SI CK1A1.LR CK1A1.TR CK1A1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CK1A1.head, CK1A1.hl, by norm_num, CK1A1.hs,
    by decide +kernel,
    O_of_wordGA chK1A1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chK2A2_K : ChainK chK2A2 20 3 CK2A2.BP 11 CK2A2.S CK2A2.SI CK2A2.LR CK2A2.TR CK2A2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CK2A2.head, CK2A2.hl, by norm_num, CK2A2.hs,
    by decide +kernel,
    O_of_wordGA chK2A2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chL_K : ChainK chL 18 5 CL.BP 11 CL.S CL.SI CL.LR CL.TR CL.TRI :=
  ⟨by decide, by decide, by decide +kernel, CL.head, CL.hl, by norm_num, CL.hs, by decide +kernel,
    O_of_wordGA chL (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chB12_K : ChainK chB12 5 3 CB12.BP 11 CB12.S CB12.SI CB12.LR CB12.TR CB12.TRI :=
  ⟨by decide, by decide, by decide +kernel, CB12.head, CB12.hl, by norm_num, CB12.hs,
    by decide +kernel,
    O_of_wordGA chB12 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chB23_K : ChainK chB23 4 1 CB23.BP 11 CB23.S CB23.SI CB23.LR CB23.TR CB23.TRI :=
  ⟨by decide, by decide, by decide +kernel, CB23.head, CB23.hl, by norm_num, CB23.hs,
    by decide +kernel,
    O_of_wordGA chB23 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chSJ_K : ChainK chSJ 6 3 CSJ.BP 11 CSJ.S CSJ.SI CSJ.LR CSJ.TR CSJ.TRI :=
  ⟨by decide, by decide, by decide +kernel, CSJ.head, CSJ.hl, by norm_num, CSJ.hs,
    by decide +kernel,
    O_of_wordGA chSJ (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chT1_K : ChainK chT1 6 2 CT1.BP 11 CT1.S CT1.SI CT1.LR CT1.TR CT1.TRI :=
  ⟨by decide, by decide, by decide +kernel, CT1.head, CT1.hl, by norm_num, CT1.hs,
    by decide +kernel,
    O_of_wordGA chT1 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

theorem chT2_K : ChainK chT2 6 2 CT2.BP 11 CT2.S CT2.SI CT2.LR CT2.TR CT2.TRI :=
  ⟨by decide, by decide, by decide +kernel, CT2.head, CT2.hl, by norm_num, CT2.hs,
    by decide +kernel,
    O_of_wordGA chT2 (by unfold ChainData.GensOK; decide) hG hc hid hidA (by decide +kernel)⟩

end CertificateChecks.KernelU6.Sec3
