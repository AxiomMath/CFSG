module

public import Certificates.Kernel.TwoHS.HYOps
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def SG (i : Fin 6) : Nat := WK (sigWords.getD i.val [])

@[expose] noncomputable def SGI (i : Fin 6) : Nat := WKI (sigWords.getD i.val [])

theorem sig_inv : (List.finRange 6).all (fun i =>
    invEqK 11200 14 (mask 14) (11200 * 14) (SG i) (SGI i)) = true := by quickRfl

theorem sig_rels_cox : hsCoxeter.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (pc (SG i) (EVK SG SGI r)) (pc (EVK SG SGI r) (SG i))) = true := by quickRfl

theorem sig_rels_extra : hsExtra.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (pc (SG i) (EVK SG SGI r)) (pc (EVK SG SGI r) (SG i))) = true := by quickRfl

theorem sig_comm : (List.finRange 6).all (fun i =>
    Nat.beq (EVK SG SGI (hsCommWord i)) (SG i)) = true := by quickRfl

theorem sig_sq0 : Nat.beq (WK (sigWord (sigWords.getD 0 []))) (HY.F 0) = true := by quickRfl
theorem sig_sq1 : Nat.beq (WK (sigWord (sigWords.getD 1 []))) (HY.F 1) = true := by quickRfl
theorem sig_sq2 : Nat.beq (WK (sigWord (sigWords.getD 2 []))) (HY.F 2) = true := by quickRfl
theorem sig_sq3 : Nat.beq (WK (sigWord (sigWords.getD 3 []))) (HY.F 3) = true := by quickRfl
theorem sig_sq4 : Nat.beq (WK (sigWord (sigWords.getD 4 []))) (HY.F 4) = true := by quickRfl
theorem sig_sq5 : Nat.beq (WK (sigWord (sigWords.getD 5 []))) (HY.F 5) = true := by quickRfl

theorem sig_fix : (fx (WK outerWord) != fx (WK (sigWord outerWord))) = true := by quickRfl

end CFSG.KD.TwoHS

end
