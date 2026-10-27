module

public import Certificates.Kernel.HN1408.M11Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog

theorem kHA : headM [y0Word, vWord] 2 7920 MR1.G MR1.GI MR1I MR1.T MR1.PL MR1.cnt = true := by
  quickRfl
theorem kYP : allN 12 (fun k => Nat.beq (MYP k) (ppK (WK y0Word) k)) = true := by quickRfl
theorem kG : allN 7 (fun j => Nat.beq (pc (WK [j + 1]) (WK [j + 1])) idK) = true := by quickRfl
theorem kVW : Nat.beq (WK vWordYI) (WK vWord) = true := by quickRfl

@[expose] def invWs : List (List Nat) := [y0Word, vWord, n1Word, ck2Word, ck3Word, ck4Word, cBWord]

theorem kInv : allN 7 (fun j => bAnd(canonK 1408 11 (mask 11) (1408 * 11) (MInv j),
    invEqK 1408 11 (mask 11) (1408 * 11) (WK (invWs.getD j [])) (MInv j))) = true := by
  quickRfl

theorem kY : bAnd(Nat.beq (ppK (WK y0Word) 11) idK, bIf(Nat.beq (WK y0Word) idK, false, true)) =
    true := by
  quickRfl
theorem kV : bAnd(Nat.beq (ppK (WK vWord) 11) idK, bIf(Nat.beq (WK vWord) idK, false, true)) =
    true := by
  quickRfl
theorem kYV : bIf(commP (WK y0Word) (WK vWord), false, true) = true := by quickRfl
theorem kRel : allN 2 (fun r => Nat.beq (relK (WK y0Word) (WK vWord) (MInv 0) (MInv 1)
    (m11Relators.getD r [])) idK) = true := by
  quickRfl

theorem kI0 : bAnd(Nat.beq (ppK (WK i0Word) 2) idK, bIf(Nat.beq (WK i0Word) idK, false, true)) =
    true := by
  quickRfl

theorem kW : allN 5 (fun j => bAnd(Nat.blt (MW j) MR1.cnt, Nat.beq (MR1.T (MW j))
    (WK ([i0Word, rho0Word, ck2Word, ck3Word, ck4Word].getD j [])))) = true := by
  quickRfl

theorem kN1 : Nat.beq (pc (pc (WK n1Word) (WK y0Word)) (MInv 2)) (ppK (WK y0Word) 7) = true := by
  quickRfl

theorem kR : bAnd(Nat.beq (ppK (WK rho0Word) 5) idK, bIf(Nat.beq (WK rho0Word) idK, false, true)) =
    true := by
  quickRfl
theorem kC : allN 3 (fun j => Nat.beq (pc (pc (WK ([ck2Word, ck3Word, ck4Word].getD j []))
    (WK rho0Word)) (MInv (j + 3))) (ppK (WK rho0Word) (j + 2))) = true := by
  quickRfl
theorem kCB : Nat.beq (pc (pc (WK cBWord) (WK rho0Word)) (MInv 6)) (WK fix5B.rep) = true := by
  quickRfl

end CFSG.KD.HN1408

end
