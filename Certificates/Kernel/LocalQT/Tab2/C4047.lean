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
public import Certificates.Kernel.LocalQT.Tab2.RecK

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

#lqt_t2_rec CFSG.KD.LQT.C4047 23 CFSG.QuasithinUnique.Unc25G2.M2x.d23 CFSG.KD.LQT.C4047.clS
  CFSG.KD.LQT.C4047.hS CFSG.KD.LQT.C4047.pS

namespace CFSG.KD.LQT.C4047

open CFSG.KC.LQT.T2 CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.M2x
open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KD.LQT.T2Rec

theorem h₁ : d23.clPar = parsePairs (String.ofList CL.chars) := by rw [← CL.eq]; rfl
theorem h₂ : d23.hPar = parsePairs (String.ofList HL.chars) := by rw [← HL.eq]; rfl
theorem h₃ : d23.pPar = parsePairs (String.ofList PL.chars) := by rw [← PL.eq]; rfl
theorem r_cl : someB (parseK CL.chars) CPr = true := by quickRfl
theorem r_h : someB (parseK HL.chars) HPr = true := by quickRfl
theorem r_p : someB (parseK PL.chars) PPr = true := by quickRfl
theorem r_A : Nat.beq (codeT d23.ta) Ar = true := by quickRfl
theorem r_B : Nat.beq (codeT d23.tb) Br = true := by quickRfl
theorem r_CL : eqLB (bfsQ (fun x g => mul 23 (mul 23 g x) (inv 23 g)) (one 23)
    [Ar, Br, inv 23 Ar, inv 23 Br] Ar CPr) CLr = true := by quickRfl
theorem r_HL : eqLB (bfsQ (mul 23) (one 23) (List.map (wordK 23 Ar Br) d23.hGensW) (one 23) HPr)
    HLr = true := by quickRfl
theorem r_PL : eqLB (bfsQ (mul 23) (one 23) (List.map (wordK 23 Ar Br) d23.pGensW) (one 23) PPr)
    PLr = true := by quickRfl
theorem r_EA : eqLB (spanK 23 (List.map codeT d23.eaGens)) EAr = true := by quickRfl
theorem r_EB : eqLB (spanK 23 (List.map codeT d23.ebGens)) EBr = true := by quickRfl

theorem k01 : monoK CPr = true := by quickRfl
theorem k02 : monoK HPr = true := by quickRfl
theorem k03 : monoK PPr = true := by quickRfl
theorem k04 : tabOK 23 d23.ta = true := by quickRfl
theorem k05 : tabOK 23 d23.tb = true := by quickRfl
theorem k06 : allT d23.eaGens (tabOK 23) = true := by quickRfl
theorem k07 : allT d23.ebGens (tabOK 23) = true := by quickRfl
theorem k08 : distinctS CLr = true := by quickRfl
theorem k09 : distinctS HLr = true := by quickRfl
theorem k10 : Nat.beq (Nat.mul (lenL CLr) (lenL HLr)) d23.order = true := by quickRfl
theorem k11 : allL HLr (fun h => comm 23 h Ar) = true := by quickRfl
theorem k12 : distinctL PLr = true := by quickRfl
theorem k13 : Nat.beq (lenL PLr) 128 = true := by quickRfl
theorem k14 : Nat.beq (Nat.mod (Nat.div d23.order 128) 2) 1 = true := by quickRfl
theorem k15 : closedT 23 PLr = true := by quickRfl
theorem k16 : closedT 23 EAr = true := by quickRfl
theorem k17 : closedT 23 EBr = true := by quickRfl
theorem k18 : eokT 23 PLr EAr = true := by quickRfl
theorem k19 : eokT 23 PLr EBr = true := by quickRfl
theorem k20 : memL Ar EAr = true := by quickRfl
theorem k21 : memL Ar EBr = true := by quickRfl
theorem k22 : anyL EAr (fun t => notB (memL t EBr)) = true := by quickRfl
theorem k23 : selfCentT 23 HLr EAr = true := by quickRfl
theorem k24 : selfCentT 23 HLr EBr = true := by quickRfl
theorem k25 : witT 23 (wordK 23 Ar Br d23.gaW) EAr EBr = true := by quickRfl
theorem k26 : witT 23 (wordK 23 Ar Br d23.gbW) EBr EAr = true := by quickRfl
theorem k27 : classT 23 PLr EAr EBr = true := by quickRfl

theorem hk : checkK 23 d23.ta d23.tb d23.order CL.chars d23.hGensW HL.chars d23.pGensW
    PL.chars d23.eaGens d23.ebGens d23.gaW d23.gbW = true :=
  checkK_of (eq_of_someB r_cl) (eq_of_someB r_h) (eq_of_someB r_p) (Nat.eq_of_beq_eq_true r_A)
    (Nat.eq_of_beq_eq_true r_B) (eq_of_eqLB r_CL) (eq_of_eqLB r_HL) (eq_of_eqLB r_PL)
    (eq_of_eqLB r_EA) (eq_of_eqLB r_EB)
    (by rw [k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17,
      k18, k19, k20, k21, k22, k23, k24, k25, k26, k27] <;> rfl)

end CFSG.KD.LQT.C4047

end
