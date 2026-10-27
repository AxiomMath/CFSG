module

public import Certificates.Kernel.LocalQT.Pipe.F4050
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4050

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.BC CFSG.KC.LQT.PP
open CFSG.QuasithinUnique.Setup.X1

theorem hT : treeK 4725 (chunksK parC) (chunksK genC) = true := by quickRfl
theorem hI : invK 315 9 (chunksK taC) (chunksK tbC) (chunksK taiC) (chunksK tbiC) = true := by
  quickRfl
theorem hA : aszK 4725 (chunksK AaC) (chunksK AbC) = true := by quickRfl
theorem hX : xsK 4725 j2Data.xs.toList = true := by quickRfl
theorem hE : enumK 315 9 (chunksK taC) (chunksK tbC) j2Data.prog j2Data.qp 7 100000 dR RL = true :=
  by quickRfl
theorem hPa : permK 4725 (chunksK AaC) = true := by quickRfl
theorem hPb : permK 4725 (chunksK AbC) = true := by quickRfl
theorem hat : tabL 4725 (chunksK AaC) = true := by quickRfl
theorem hbt : tabL 4725 (chunksK AbC) = true := by quickRfl
theorem hpt : tabL 4725 (chunksK parC) = true := by quickRfl
theorem hgt : tabL 4725 (chunksK genC) = true := by quickRfl
theorem hrt : tabL 4725 (chunksK repC) = true := by quickRfl
theorem h0 : Nat.beq (codeK 13 (chunksK AaC)) (TF 0) = true := by quickRfl
theorem h1 : Nat.beq (codeK 13 (chunksK AbC)) (TF 1) = true := by quickRfl
theorem hPK : Nat.beq (codeK 13 (chunksK parC)) PRK = true := by quickRfl
theorem hGK : Nat.beq (codeK 13 (chunksK genC)) GNK = true := by quickRfl
theorem hRK : Nat.beq (codeK 13 (chunksK repC)) RPK = true := by quickRfl
theorem hso : slpOKK j2Data.prog 2 = true := by quickRfl
theorem hsn : slpNeedK j2Data.prog SL = true := by quickRfl
theorem hq : allA j2Data.qp (fun p => anyL SL (Nat.beq p.1)) = true := by quickRfl
theorem hid : idK 4725 13 (MF 0) = true := by quickRfl
theorem hM : needP 13 PRK ML = true := by quickRfl
theorem hRM : allL REPS (fun x => orB (Nat.beq x 0) (anyL ML (Nat.beq x))) = true := by quickRfl
theorem hXM : allA j2Data.xs.toList
    (fun l => allL l fun x => orB (Nat.beq x 0) (anyL ML (Nat.beq x))) = true := by quickRfl
theorem hrs : repsSumK 4725 REPS OML = true := by quickRfl
theorem hsh : shapeK 4725 BM SH1 SH2 = true := by quickRfl

end CFSG.KD.LQT.C4050

end
