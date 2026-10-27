module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Data.Kernel.PermCent.U33Cover
meta import Certificates.Data.Kernel.PermCent.U33Cover

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#left_orb CertificateChecks.KernelPermCent.U33.PE CFSG.GH74.KGroups.U33.Cover.genL 28 5
  CFSG.GH74.KGroups.U33.Cover.baseL 1008

#conj_orb CertificateChecks.KernelPermCent.U33.CA CFSG.GH74.KGroups.U33.Cover.genL 28 5
  CFSG.GH74.KGroups.U33.Cover.baseL 63 roots CFSG.GH74.KGroups.U33.Cover.repAL gens 2

#conj_orb CertificateChecks.KernelPermCent.U33.CB CFSG.GH74.KGroups.U33.Cover.genL 28 5
  CFSG.GH74.KGroups.U33.Cover.baseL 252 roots CFSG.GH74.KGroups.U33.Cover.repBL gens 2

#left_orb CertificateChecks.KernelPermCent.U33.SH CFSG.GH74.KGroups.U33.Cover.sylL 28 5
  CFSG.GH74.KGroups.U33.Cover.baseL 64

public section

namespace CertificateChecks.KernelPermCent.U33

open CFSG.GH74.KGroups.U33.Cover CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin

@[expose] noncomputable def at5 (p i : Nat) : Nat := pg 5 (mask 5) p i

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 28 5 (mask 5) p q

@[expose] noncomputable def tabOK (a : Array Nat) (p : Nat) : Bool :=
  (List.range 28).all fun i => Nat.beq (at5 p i) a[i]!

@[expose] noncomputable def eqF (p q : Nat) : Bool :=
  (List.range 28).all fun i => Nat.beq (at5 p i) (at5 q i)

@[expose] noncomputable def isId (p : Nat) : Bool := (List.range 28).all fun i => Nat.beq (at5 p i) i

@[expose] noncomputable def memP (p : Nat) : Bool := (List.range 6048).any fun i => Nat.beq (PE.T i) p

@[expose] noncomputable def pU : Nat := SH.G 3

theorem binds : tabOK genL[0]! (PE.G 0) = true ∧ tabOK genL[1]! (PE.G 1) = true ∧
    tabOK genL[0]! (CA.G 0) = true ∧ tabOK genL[1]! (CA.G 1) = true ∧
    tabOK genL[0]! (CB.G 0) = true ∧ tabOK genL[1]! (CB.G 1) = true ∧
    (List.range 6).all (fun k => tabOK sylL[k]! (SH.G k)) = true ∧
    Nat.beq (CA.T CA.r0) (SH.G 0) = true ∧ Nat.beq (CB.T CB.r0) (SH.G 3) = true ∧
    isId (PE.T 0) = true ∧ isId (SH.T 0) = true ∧ PE.N = 6048 ∧ CA.N = 63 ∧ CB.N = 252 ∧
    SH.N = 64 ∧ PE.ng = 2 ∧ CA.ng = 2 ∧ CB.ng = 2 ∧ SH.ng = 6 ∧ CA.r0 < 63 ∧ CB.r0 < 252 := by
  decide +kernel

theorem outer : ((List.range 6048).all fun i =>
      !Nat.beq (pkeyK 28 5 baseL (PE.T i)) (pkeyK 28 5 baseL pU)) = true ∧
    isId (pc pU pU) = true ∧ memP (pc pU (pc (PE.G 0) pU)) = true ∧
    memP (pc pU (pc (PE.G 1) pU)) = true ∧
    (List.range 6).all (fun k => memP (SH.G k) || memP (pc (SH.G k) pU)) = true := by
  decide +kernel

theorem trans : ((List.range 28).all fun x =>
    (List.range 6048).any fun i => Nat.beq (at5 (PE.T i) 0) x) = true := by
  decide +kernel

theorem stab : ((List.range 28).all fun x => Nat.beq x 0 ||
    (List.range 6048).any fun i =>
      Nat.beq (at5 (PE.T i) 0) 0 && !Nat.beq (at5 (PE.T i) x) x) = true := by
  decide +kernel

@[expose] noncomputable def wy (x h hI : Nat) : Nat := pc x (pc h (pc x hI))

theorem witA : memP xA = true ∧ memP hA = true ∧ memP hAI = true ∧
    eqF (pc xA (SH.G 0)) (pc (SH.G 0) xA) = true ∧ eqF (pc hA (SH.G 0)) (pc (SH.G 0) hA) = true ∧
    isId (pc xA (pc xA xA)) = true ∧ isId xA = false ∧ isId (pc hA hAI) = true ∧
    isId (pc (pc (wy xA hA hAI) (wy xA hA hAI)) (pc (wy xA hA hAI) (wy xA hA hAI))) = true ∧
    isId (pc (wy xA hA hAI) (wy xA hA hAI)) = false := by
  decide +kernel

theorem witB : memP xB = true ∧ memP hB = true ∧
    eqF (pc xB pU) (pc pU xB) = true ∧ eqF (pc hB pU) (pc pU hB) = true ∧
    isId (pc xB (pc xB xB)) = true ∧ isId xB = false ∧ isId (pc hB hB) = true ∧
    isId (pc (wy xB hB hB) (wy xB hB hB)) = true ∧ isId (wy xB hB hB) = false := by
  decide +kernel

@[expose] noncomputable def invol (t : Nat) : Bool := isId (pc t t) && !isId t

@[expose] noncomputable def inClasses (a b : Bool) (t : Nat) : Bool :=
  (a && (List.range 63).any fun j => Nat.beq (CA.T j) t) ||
    (b && (List.range 252).any fun j => Nat.beq (CB.T j) t)

@[expose] noncomputable def coverK (a b : Bool) (m : Nat) : Bool :=
  (List.range m).all fun i => !invol (SH.T i) || inClasses a b (SH.T i)

theorem cover : coverK true true 64 = true := by decide +kernel

theorem ucover : inClasses true true (pc pU (pc (SH.G 0) pU)) = true ∧
    inClasses true true (pc pU (pc pU pU)) = true := by
  decide +kernel

theorem neg : (!coverK true false 64 && !coverK false true 64 && !memP pU &&
    !invol (PE.T 0)) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U33

end
