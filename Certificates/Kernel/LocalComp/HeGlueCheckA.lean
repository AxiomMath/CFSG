module

public import Certificates.Kernel.LocalComp.HeGlueDefs
public import Certificates.Kernel.LocalComp.HeModelData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.ComponentClassification.AS81.HeTri CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.KC.BfsPin CertificateChecks.KernelLC.HeModel

@[expose] noncomputable def gensOK (n w g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k))

theorem kPins : (bindArrsK heP12Gens 64 7 HeMP12.ng HeMP12.G &&
    bindArrsK heB0Gens 64 7 HeMB0.ng HeMB0.G && bindArrsK heP23Gens 64 7 HeMP23.ng HeMP23.G &&
    bindArrsK heP12CGens 32 6 2 HeMP0.G && bindArrsK heP13CGens 32 6 2 HeMP1.G &&
    bindArrsK heBCGens 32 6 HeMBC.ng HeMBC.G && gensOK 64 7 HeMP12.ng HeMP12.G &&
    gensOK 64 7 HeMB0.ng HeMB0.G && gensOK 64 7 HeMP23.ng HeMP23.G && gensOK 32 6 2 HeMP0.G &&
    gensOK 32 6 2 HeMP1.G && gensOK 32 6 HeMBC.ng HeMBC.G &&
    keysSK 64 7 base64 HeMP12.N HeMP12.T skP12 && keysSK 64 7 base64 HeMB0.N HeMB0.T skB0 &&
    keysSK 64 7 base64 HeMP23.N HeMP23.T skP23 && keysSK 32 6 base32 HeMP0.N HeMP0.T skP0 &&
    keysSK 32 6 base32 HeMP1.N HeMP1.T skP1 && keysSK 32 6 base32 HeMBC.N HeMBC.T skBC) = true := by
  quickRfl

theorem kId : permOK 64 7 (mask 7) (64 * 7) (pidn 64 7) (pidn 64 7) = true ∧
    permOK 32 6 (mask 6) (32 * 6) (pidn 32 6) (pidn 32 6) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kBind : (bindArrsK heRepE 64 7 8 hd.RE && bindArrsK heRepF 64 7 8 hd.RF &&
    bindArrsK heConjF 64 7 4 hd.CF && bindArrsK hePiEArrs.toList 64 7 8 hd.PE &&
    bindArrsK hePiFArrs.toList 64 7 8 hd.PF && bindArrsK (hePiCArrs false).toList 32 6 8 hd.PC0 &&
    bindArrsK (hePiCArrs true).toList 32 6 8 hd.PC1 && bindArrsK hexaTGens 64 7 hd.gT hd.GT &&
    bindArrsK hexaMGens 64 7 hd.gM hd.GM && bindArrsK hexaR0Gens 64 7 hd.gR hd.GR &&
    bindArrsK hePCGens 32 6 hd.gC hd.GC && bindArrK hexaT0 64 7 hd.t0 &&
    bindArrK heTCArr 32 6 hd.tc) = true := by quickRfl

theorem kInv : invsK hd = true := by quickRfl

theorem kPerm : permsK hd = true := by quickRfl

theorem kSrc : srcK hd heRelsP = true := by quickRfl

theorem kRepF : repFK hd = true := by quickRfl

theorem kMem : memK hd = true := by quickRfl

theorem kPi : piK hd heWordsE heWordsF heWordsBE heWordsBF = true := by quickRfl

theorem kGen : genK hd heGenWordsC0 heGenWordsC1 heGenWordsT heGenWordsM heGenWordsR = true := by
  quickRfl

theorem kWB : wordsBK hd (heWordsBE ++ heWordsBF) = true := by quickRfl

theorem kKerE : relsK 64 7 8 hd.PE hd.PEI hePiRels23Codes = true := by quickRfl

theorem kNorm : normCnt hd 0 3072 = 1024 := Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] noncomputable def wX (k s : Nat) : Nat := HeGlueD.WX (Nat.add (Nat.mul 64 k) s)

theorem kFus : allN 15 (fun k => fusK hd (heWit.getD (4 * k) [])
    (heWit.getD (4 * k + 1) []) (heWit.getD (4 * k + 2) []) (heWit.getD (4 * k + 3) [])
    (heWitE.getD k true) k (HeGlueD.WF k) (HeGlueD.WM k) (wX k)) = true := by quickRfl

theorem kRange : heCheckRange = true := by decide +kernel

end CertificateChecks.KernelLC.HeGlue

end
