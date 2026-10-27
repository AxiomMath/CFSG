module

public import Certificates.Kernel.LocalComp.HeModelCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HexaKSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.HeModelK CFSG.KC.Enum CFSG.KS
open CFSG.KS.Prim CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri CertificateChecks.KernelLC
open CertificateChecks.KernelLC.BindL CertificateChecks.KernelLC.HeModel
open CertificateChecks.KernelLC.HexaOrb (PT0)

theorem kBind64 : (bindL hexaTGens 64 7 HexaT.ng HexaT.G && bindL hexaMGens 64 7 HexaM.ng HexaM.G &&
    bindL hexaCGens 64 7 HexaC.ng HexaC.G &&
    bindL (hexaTGens ++ hexaCGens) 64 7 HeMP12.ng HeMP12.G &&
    bindL heB0Gens 64 7 HeMB0.ng HeMB0.G && bindL heF0Gens 64 7 HeMF0.ng HeMF0.G &&
    bindL heP23Gens 64 7 HeMP23.ng HeMP23.G) = true := by quickRfl

theorem kBind32 : (bindL hePCGens 32 6 HeMC.ng HeMC.G && bindL heBCGens 32 6 HeMBC.ng HeMBC.G &&
    bindL heP12CGens 32 6 HeMP0.ng HeMP0.G && bindL heP13CGens 32 6 HeMP1.ng HeMP1.G &&
    bindL heECGens 32 6 HeMU0.ng HeMU0.G && bindL heFCGens 32 6 HeMU1.ng HeMU1.G) = true := by
  quickRfl

theorem kPerm64 : (gensP 64 7 HexaT.ng HexaT.G && gensP 64 7 HexaM.ng HexaM.G &&
    gensP 64 7 HexaC.ng HexaC.G && gensP 64 7 HeMP12.ng HeMP12.G && gensP 64 7 HeMB0.ng HeMB0.G &&
    gensP 64 7 HeMF0.ng HeMF0.G && gensP 64 7 HeMP23.ng HeMP23.G) = true := by quickRfl

theorem kPerm32 : (gensP 32 6 HeMC.ng HeMC.G && gensP 32 6 HeMBC.ng HeMBC.G &&
    gensP 32 6 HeMP0.ng HeMP0.G && gensP 32 6 HeMP1.ng HeMP1.G && gensP 32 6 HeMU0.ng HeMU0.G &&
    gensP 32 6 HeMU1.ng HeMU1.G) = true := by quickRfl

theorem kKeys64 : (keysSK 64 7 base64 HexaT.N HexaT.T skT && keysSK 64 7 base64 HexaM.N HexaM.T skM &&
    keysSK 64 7 base64 HeMP12.N HeMP12.T skP12 && keysSK 64 7 base64 HeMB0.N HeMB0.T skB0 &&
    keysSK 64 7 base64 HeMF0.N HeMF0.T skF0) = true := by quickRfl

theorem kKeysP23 : keysSK 64 7 base64 HeMP23.N HeMP23.T skP23 = true := by quickRfl

theorem kKeysC : keysSK 32 6 base32 HeMC.N HeMC.T skC = true := by quickRfl

theorem kKeys32 : (keysSK 32 6 base32 HeMBC.N HeMBC.T skBC && keysSK 32 6 base32 HeMP0.N HeMP0.T skP0 &&
    keysSK 32 6 base32 HeMP1.N HeMP1.T skP1 && keysSK 32 6 base32 HeMU0.N HeMU0.T skU0 &&
    keysSK 32 6 base32 HeMU1.N HeMU1.T skU1) = true := by quickRfl

theorem kZT : (bindArrK heZetaArr 64 7 PZ && permOK 64 7 (mask 7) (64 * 7) PZ (pinvS 64 7 (mask 7) PZ) &&
    bindArrK hexaT0 64 7 PT0 && permOK 64 7 (mask 7) (64 * 7) PT0 (pinvS 64 7 (mask 7) PT0) &&
    bindArrK heTCArr 32 6 PTC && permOK 32 6 (mask 6) (32 * 6) PTC (pinvS 32 6 (mask 6) PTC)) = true := by
  quickRfl

theorem kZeta : zetaK 7 d64.NT d64.TT d64.NM d64.TM PZ = true := by quickRfl

theorem kB0 : b0K d64 = true := by quickRfl

theorem kFB : flagsK 64 7 d64.NB d64.TB (pidn 64 7) d64.FB d64.FB = true := by quickRfl

theorem kC : cK d32 = true := by quickRfl

theorem kFBC : flagsK 32 6 d32.NBC d32.TBC (pidn 32 6) d32.FBC d32.FBC = true := by quickRfl

theorem kCount : CFSG.KC.HeModelK.countK d32 = true := by quickRfl

end CertificateChecks.KernelLC.HeModelCheck

end
