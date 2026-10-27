module

public import Certificates.Kernel.HN25550.Data
public import Certificates.Kernel.HN25550.Checks
public import Certificates.Data.Kernel.Spor.WordRegs
public import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Sporadic.HNSchreier.LocalData
public import CFSG.Sporadic.HNOddCore.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HN25550

open CFSG.KS.WordRegs CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] def r0 : Nat → List Nat := fun r => if r = 1 then [1] else if r = 2 then [3] else []

@[expose] def lettersJ (j : Nat) (w : List Int) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ j)

@[expose] def g6code (G6S G6 : List Nat) (s : Nat) : Nat := 2 * G6.getD (G6S.idxOf s) 0 + 1

@[expose] def tiesK (RW REL : List (List Nat)) (SP HJ C6J C6 : List Nat) (U HC G6C : Nat)
    (M2 : List Nat) (M2R1 E61 : Nat) (G6S G6 : List Nat) (PW : List (List Nat)) (PR : List Nat) :
    Bool :=
  let K := HJ.map fun g => 2 * g + 1
  RW.length == 44 && REL.length == 44 && rootsOK RW &&
  ((List.range 44).all fun k => REL.getD k [] == RW.getD k [] ++ [2 * (k + 2)]) &&
  triOK RW r0 CFSG.Sporadic.HNSchreier.Data.subgroupProgram SP &&
  tieW RW (triRegs r0 CFSG.Sporadic.HNSchreier.Data.subgroupProgram SP 1) (K.getD 0 0) &&
  tieW RW (triRegs r0 CFSG.Sporadic.HNSchreier.Data.subgroupProgram SP 2) (K.getD 1 0) &&
  HJ.length == 17 &&
  ((List.range 15).all fun u =>
    tieW RW ((CFSG.Sporadic.HNSchreier.LocalData.strongWords[u + 2]!).map (sgnC K))
      (K.getD (u + 2) 0)) &&
  C6J == [1, 2, 5] && C6.length == 3 &&
  ((List.range 3).all fun k =>
    lettersJ 17 CFSG.Sporadic.HNOddCore.InvData.c6Words[C6J.getD k 0]! &&
    tieW RW ((CFSG.Sporadic.HNOddCore.InvData.c6Words[C6J.getD k 0]!).map (sgnC K))
      (2 * C6.getD k 0 + 1)) &&
  tieW RW (CFSG.Sporadic.HNOddCore.InvData.m2ConjRoot.map fun l => if l = 1 then 1 else 3)
    (2 * U + 1) &&
  lettersJ 17 CFSG.Sporadic.HNOddCore.InvData.m2ConjH &&
  tieW RW (CFSG.Sporadic.HNOddCore.InvData.m2ConjH.map (sgnC K)) (2 * HC + 1) &&
  tieW RW [2 * U + 1, 2 * HC + 1] (2 * G6C + 1) &&
  bprOK RW r0 CFSG.Sporadic.HNOddCore.InvData.m2Prog M2 &&
  tieW RW (bprRegs r0 CFSG.Sporadic.HNOddCore.InvData.m2Prog M2 1) M2R1 &&
  tieW RW [2 * G6C, M2R1, 2 * G6C + 1] (2 * E61 + 1) &&
  G6S == [1, 2, 5, 10] && G6 == [C6.getD 0 0, C6.getD 1 0, C6.getD 2 0, E61] &&
  PW.length == 4 && PR.length == 4 &&
  ((List.range 4).all fun j =>
    tieW RW ((PW.getD j []).map (g6code G6S G6)) (2 * PR.getD j 0 + 1) &&
      decide (PR.getD j 0 < 46))

theorem ties_ok : tiesK RW REL SP HJ C6J C6 U HC G6C M2 M2R1 E61 G6S G6 PW PR = true := by
  decide +kernel

theorem gcan : allN 4 (fun j => canonK 1100 11 (mask 11) (1100 * 11) (EP.G j)) = true := by
  quickRfl

theorem neg_ties : Bool.not (tiesK RW REL SP HJ C6J C6 U HC G6C M2 M2R1 E61 G6S
    [C6.getD 1 0, C6.getD 0 0, C6.getD 2 0, E61] PW PR) = true := by
  decide +kernel

theorem neg_ties_hj : Bool.not (tiesK RW REL SP
    (HJ.set 2 (HJ.getD 3 0) |>.set 3 (HJ.getD 2 0)) C6J C6 U HC G6C M2 M2R1 E61 G6S G6 PW PR) =
    true := by
  decide +kernel

end CFSG.KD.HN25550

end
