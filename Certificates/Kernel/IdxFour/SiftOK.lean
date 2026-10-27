module

public import Certificates.Kernel.IdxFour.E0Data
public import Certificates.Kernel.IdxFour.M0Data
public import Certificates.Kernel.IdxFour.SiftData
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Inputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4R

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.IdxFour

theorem cf17605sift :
    recsOK CFSG.KD.IF4E.T CFSG.KD.IF4E.O 1 (fun _ => idP)
      ((pGens ++ E0Chk.sGensE0).map packR) P5 = true := by
  decide +kernel

theorem cf17609sift :
    recsOK CFSG.KD.IF4E.T CFSG.KD.IF4E.O 4 (look CFSG.KD.IF4M.Q)
      ((sGens ++ lbarGens).map packR) P9 = true := by
  decide +kernel

theorem cf17611sift :
    recsOK CFSG.KD.IF4E.T CFSG.KD.IF4E.O 1 (fun _ => idP)
      [packR (lbarGens.getD 3 #[]), mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 1 #[])),
        mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 2 #[])),
        mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 4 #[]))] P11 = true := by
  decide +kernel

theorem cf17611sk :
    recsOK CFSG.KD.IF4E.T CFSG.KD.IF4E.O 32 (subP (lbarGens.map packR))
      (skGens.map packR) PK = true := by
  decide +kernel

theorem cf17611aux :
    (lbarGens.all fun l => Nat.beq (mulP (packR l) (packR l)) idP) = true ∧
    Nat.beq (ap12 (mulP (packR (lbarGens.getD 0 #[])) (packR omegaRows)) 64)
      (ap12 (mulP (packR omegaRows) (packR (lbarGens.getD 0 #[]))) 64) = false := by
  decide +kernel

theorem cf17605aux :
    ([12, 20, 264, 36, 63].all fun b => Nat.beq (ap12 (packR s12Rows) b) b) = true ∧
    Nat.beq (ap12 (packR s12Rows) 1) 1 = false := by
  decide +kernel

end CFSG.KD.IF4R

end
