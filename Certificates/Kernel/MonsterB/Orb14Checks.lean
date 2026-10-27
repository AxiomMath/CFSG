
module

public import Certificates.Data.Kernel.MonsterB.Orb14
public import Certificates.Data.Kernel.MonsterB.BfsReplayT
public import Certificates.Kernel.MonsterB.Orb14Data
public import Certificates.Kernel.MonsterB.Orb14Net
public import Certificates.Kernel.MonsterB.Tau1408Data
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputsBase
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate3175Base

public section

namespace CertificateChecks.Orb14

open CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KLie.CT CFSG.KC.U6Orb
open CertificateChecks.Tau1408

set_option maxRecDepth 100000

theorem kSing : andB (bindL b6SingArr.toList SGL 12 693 4096)
    (andB (incOK SGL 693 12 4096) (Nat.blt 0 (fget SGL 0 12))) = true := by quickRfl

theorem kIso : bindL b6IsoArr.toList ISO 10 891 891 = true := by quickRfl

theorem kFrb : bindL b6FrobArr.toList FRB 1 17 2 = true := by quickRfl

theorem kMat : bindP b6MatArr.toList MATP 6 12 17 4096 = true := by quickRfl

theorem kPl : bindP b6PlaneArr.toList PLP 3 12 891 4096 = true := by quickRfl

theorem kNP : bindP n6PermsArr.toList NP 891 10 17 891 = true := by quickRfl

theorem kO0 : Nat.beq (bitsOf (o14PtOrb[0]!).toList) MO0 = true := by quickRfl

theorem kO1 : Nat.beq (bitsOf (o14PtOrb[1]!).toList) MO1 = true := by quickRfl

theorem kP0 : Nat.beq (bitsOf (o14PlOrb[0]!).toList) MP0 = true := by quickRfl

theorem kP1 : Nat.beq (bitsOf (o14PlOrb[1]!).toList) MP1 = true := by quickRfl

theorem kPart : andB (Nat.beq (Nat.land MO0 MO1) 0) (andB (Nat.beq (Nat.lor MO0 MO1) (maskN 693))
    (andB (Nat.beq (Nat.land MP0 MP1) 0) (Nat.beq (Nat.lor MP0 MP1) (maskN 891)))) = true := by
  quickRfl

theorem kMN0 : Nat.beq (maskB 891 fun j => bit MP0 (fget ISO j 10)) MN0 = true := by quickRfl

theorem kCard : andB (Nat.beq (popc 693 MO0) 126) (Nat.beq (popc 891 MN0) 324) = true := by
  quickRfl

theorem kXP : xpOK XP SGL = true := by quickRfl

theorem kTieS : tieS NETS XP MATP FRB = true := by quickRfl

theorem kTieN : tieN NETN NP 891 = true := by quickRfl

theorem kBase : andB (Nat.beq (fget SB 0 693) MO0) (Nat.beq (fget SBN 0 891) MN0) = true := by
  quickRfl

theorem kCovS0 : Nat.beq (cover NETS (pw2 0) 10) MO0 = true := by quickRfl

theorem kCovS1 : Nat.beq (cover NETS (pw2 2) 12) MO1 = true := by quickRfl

theorem kCovN0 : Nat.beq (cover NETN (pw2 167) 6) MN0 = true := by quickRfl

theorem kCovN1 : Nat.beq (cover NETN (pw2 0) 13) (Nat.xor (maskN 891) MN0) = true := by quickRfl

theorem kInc0 : incidOK XP PLP PU MO0 MP0 0 297 = true := by quickRfl

theorem kInc1 : incidOK XP PLP PU MO0 MP0 297 297 = true := by quickRfl

theorem kInc2 : incidOK XP PLP PU MO0 MP0 594 297 = true := by quickRfl

theorem kRep : CFSG.KC.Bfs.replayTOK (tabE 17 11 ET) (fun j => fget PT j 11) (fun j => fget LT j 5)
    17 1408 = true := by quickRfl

theorem kTreeB : (Nat.beq (fget PT 1 11) 0 && Nat.beq (fget LT 1 5) 0 && Nat.beq (fget PT 2 11) 0 &&
    Nat.beq (fget LT 2 5) 1 && Nat.beq (fget PT 4 11) 0 && Nat.beq (fget LT 4 5) 5 &&
    Nat.beq (fget PT 8 11) 0 && Nat.beq (fget LT 8 5) 12 && Nat.beq (fget PT 13 11) 1 &&
    Nat.beq (fget LT 13 5) 2) = true := by quickRfl

theorem kTree : fget PT 1 11 = 0 ∧ fget LT 1 5 = 0 ∧ fget PT 2 11 = 0 ∧ fget LT 2 5 = 1 ∧
    fget PT 4 11 = 0 ∧ fget LT 4 5 = 5 ∧ fget PT 8 11 = 0 ∧ fget LT 8 5 = 12 ∧
    fget PT 13 11 = 1 ∧ fget LT 13 5 = 2 := by
  have h := kTreeB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem kSelEB : (Nat.beq (tabE 17 11 ET 0 2) 2 && Nat.beq (tabE 17 11 ET 0 4) 0 &&
    Nat.beq (tabE 17 11 ET 0 6) 0 && Nat.beq (tabE 17 11 ET 0 7) 0 &&
    Nat.beq (tabE 17 11 ET 0 14) 8 && Nat.beq (tabE 17 11 ET 0 16) 0 &&
    Nat.beq (tabE 17 11 ET 13 3) 4) = true := by quickRfl

theorem kSelE : tabE 17 11 ET 0 2 = 2 ∧ tabE 17 11 ET 0 4 = 0 ∧ tabE 17 11 ET 0 6 = 0 ∧
    tabE 17 11 ET 0 7 = 0 ∧ tabE 17 11 ET 0 14 = 8 ∧ tabE 17 11 ET 0 16 = 0 ∧
    tabE 17 11 ET 13 3 = 4 := by
  have h := kSelEB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem kRootsB : (Nat.beq ((o14PtOrb[0]!)[0]!) 0 && Nat.beq ((o14PtOrb[1]!)[0]!) 2 &&
    Nat.beq (natOf (o14PlOrb[0]!)[0]!) 167 && Nat.beq (natOf (o14PlOrb[1]!)[0]!) 0) = true := by
  quickRfl

theorem kRoots : (o14PtOrb[0]!)[0]! = 0 ∧ (o14PtOrb[1]!)[0]! = 2 ∧ natOf (o14PlOrb[0]!)[0]! = 167 ∧
    natOf (o14PlOrb[1]!)[0]! = 0 := by
  have h := kRootsB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨a, b, c, d⟩

theorem kSel : o14PtSel = #[(0, 2), (0, 4), (0, 6), (0, 7), (0, 14), (0, 16), (13, 3)] ∧
    o14PlSel = #[(0, 2), (0, 4), (0, 6), (0, 7), (0, 14), (0, 16), (13, 3)] := ⟨rfl, rfl⟩

end CertificateChecks.Orb14

end
