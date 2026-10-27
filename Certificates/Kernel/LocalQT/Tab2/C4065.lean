module

public import Certificates.Data.Kernel.LocalQT.Tab2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22Inputs
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Certificate113

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KD.LQT.C4065

@[expose] public def clS : String := include_str "d22_clPar.txt"
@[expose] public def hS : String := include_str "d22_hPar.txt"
@[expose] public def pS : String := include_str "d22_pPar.txt"

end CFSG.KD.LQT.C4065

#ks_chars CFSG.KD.LQT.C4065.CL CFSG.KD.LQT.C4065.clS
#ks_chars CFSG.KD.LQT.C4065.HL CFSG.KD.LQT.C4065.hS
#ks_chars CFSG.KD.LQT.C4065.PL CFSG.KD.LQT.C4065.pS

public section

namespace CFSG.KD.LQT.C4065

open CFSG.KC.LQT.T2 CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.M2x

theorem h₁ : d22.clPar = parsePairs (String.ofList CL.chars) := by rw [← CL.eq]; rfl
theorem h₂ : d22.hPar = parsePairs (String.ofList HL.chars) := by rw [← HL.eq]; rfl
theorem h₃ : d22.pPar = parsePairs (String.ofList PL.chars) := by rw [← PL.eq]; rfl
theorem hk : checkK 22 d22.ta d22.tb d22.order CL.chars d22.hGensW HL.chars d22.pGensW
    PL.chars d22.eaGens d22.ebGens d22.gaW d22.gbW = true := by quickRfl

end CFSG.KD.LQT.C4065

end
