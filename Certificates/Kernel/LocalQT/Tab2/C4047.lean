module

public import Certificates.Data.Kernel.LocalQT.Tab2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23Inputs
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Sporadic.M23.M23Group
public import Certificates.Certificate113

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KD.LQT.C4047

@[expose] public def clS : String := include_str "d23_clPar.txt"
@[expose] public def hS : String := include_str "d23_hPar.txt"
@[expose] public def pS : String := include_str "d23_pPar.txt"

end CFSG.KD.LQT.C4047

#ks_chars CFSG.KD.LQT.C4047.CL CFSG.KD.LQT.C4047.clS
#ks_chars CFSG.KD.LQT.C4047.HL CFSG.KD.LQT.C4047.hS
#ks_chars CFSG.KD.LQT.C4047.PL CFSG.KD.LQT.C4047.pS

public section

namespace CFSG.KD.LQT.C4047

open CFSG.KC.LQT.T2 CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.M2x

theorem h₁ : d23.clPar = parsePairs (String.ofList CL.chars) := by rw [← CL.eq]; rfl
theorem h₂ : d23.hPar = parsePairs (String.ofList HL.chars) := by rw [← HL.eq]; rfl
theorem h₃ : d23.pPar = parsePairs (String.ofList PL.chars) := by rw [← PL.eq]; rfl
theorem hk : checkK 23 d23.ta d23.tb d23.order CL.chars d23.hGensW HL.chars d23.pGensW
    PL.chars d23.eaGens d23.ebGens d23.gaW d23.gbW = true := by quickRfl

end CFSG.KD.LQT.C4047

end
