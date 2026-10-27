module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import CFSG.LargeExtraspecial.DWInsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.LargeExtraspecial.DW.Insp

@[expose] noncomputable def dwA (i : Nat) : Nat := wO (eWords.getD i [])

@[expose] noncomputable def dwT (t : List Nat) : Nat := t.foldr (fun i u => pc (dwA i) u) pid

@[expose] noncomputable def dwC (k : Nat) (w : List Int) : Nat := pc (wO w) (ppw (AP.S 8) k)

theorem kRel : bAnd(Nat.beq (ppw (AP.S 8) 3) pid, bAnd(Nat.beq (pc (AP.S 9) (AP.S 9)) pid,
    bAnd(Nat.beq (pc (AP.S 9) (AP.S 8)) (pc (ppw (AP.S 8) 2) (AP.S 9)),
    allN 3 fun k => cn (ppw (AP.S 8) k)))) = true := by
  quickRfl

theorem kE : bAnd(allN 4 (fun i => bAnd(lettersK 17 (eWords.getD i []), bAnd(cn (dwA i),
    bAnd(Nat.beq (ppw (dwA i) 3) pid, bAnd(allN 3 (fun k => cn (ppw (dwA i) k)),
    allN 4 fun j => Nat.beq (pc (dwA i) (dwA j)) (pc (dwA j) (dwA i))))))),
    bAnd(bIf(Nat.beq (dwT [0, 1, 2]) pid, false, true),
    bAnd(Nat.beq (pc (AP.S 9) (dwA 0)) (pc (dwA 0) (AP.S 9)),
    Nat.beq (pc (AP.S 9) (dwA 1)) (pc (dwA 1) (AP.S 9))))) = true := by
  quickRfl

theorem kBW : List.all bwEntries (fun e => bAnd(List.all e.1 (fun i => Nat.blt i 4),
    bAnd(List.all (repTerms.getD e.2.2.2.1 []) (fun i => Nat.blt i 4),
    bAnd(Nat.blt e.2.1 3, bAnd(Nat.blt e.2.2.2.2 3, bAnd(lettersK 17 e.2.2.1, bAnd(cn (wO e.2.2.1),
    bAnd(cn (ppw (dwT (repTerms.getD e.2.2.2.1 [])) e.2.2.2.2),
    Nat.beq (pc (dwC e.2.1 e.2.2.1) (dwT e.1))
      (pc (ppw (dwT (repTerms.getD e.2.2.2.1 [])) e.2.2.2.2) (dwC e.2.1 e.2.2.1)))))))))) = true := by
  quickRfl

theorem kInv : allN 3 (fun i => bAnd(lettersK 17 (invData.getD i ([], [], 0)).1,
    bAnd(lettersK 17 (invData.getD i ([], [], 0)).2.1,
    bAnd(cn (wO (invData.getD i ([], [], 0)).1), bAnd(cn (wO (invData.getD i ([], [], 0)).2.1),
    bAnd(List.all (repTerms.getD (invData.getD i ([], [], 0)).2.2 []) (fun i => Nat.blt i 4),
    bAnd(Nat.beq (pc (wO (invData.getD i ([], [], 0)).1) (wO (invData.getD i ([], [], 0)).2.1))
      (pc (dwT (repTerms.getD (invData.getD i ([], [], 0)).2.2 [])) (wO (invData.getD i ([], [], 0)).1)),
    Nat.beq (pc (mainK i) (pc (wO (invData.getD i ([], [], 0)).2.1)
      (pc (mainK i) (wO (invData.getD i ([], [], 0)).2.1)))) pid))))))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
