module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Data.Kernel.PermCent.U52Cover
meta import Certificates.Data.Kernel.PermCent.U52Cover
import all CFSG.Fischer.F4

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#conj_orb CertificateChecks.KernelPermCent.U52.CA CFSG.ComponentClassification.GSThmB.U52.Cover.genL
  341 9 CFSG.ComponentClassification.GSThmB.U52.Cover.baseL 165
  roots CFSG.ComponentClassification.GSThmB.U52.Cover.repAL gens 2

#conj_orb CertificateChecks.KernelPermCent.U52.CB CFSG.ComponentClassification.GSThmB.U52.Cover.genL
  341 9 CFSG.ComponentClassification.GSThmB.U52.Cover.baseL 330
  roots CFSG.ComponentClassification.GSThmB.U52.Cover.repBL gens 2

#left_orb CertificateChecks.KernelPermCent.U52.SH CFSG.ComponentClassification.GSThmB.U52.Cover.sylL
  341 9 CFSG.ComponentClassification.GSThmB.U52.Cover.baseL 256

public section

namespace CertificateChecks.KernelPermCent.U52

open CFSG.ComponentClassification.GSThmB.U52 CFSG.ComponentClassification.GSThmB.U52.Cover
open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def matOK (k p : Nat) : Bool :=
  (List.range 341).all fun i => Nat.beq (pg 9 (mask 9) p i) (ptIndex (mv5 (matN k) (decode i)))

theorem binds : matOK codeA (CA.G 0) = true ∧ matOK codeB (CA.G 1) = true ∧
    matOK codeA (CB.G 0) = true ∧ matOK codeB (CB.G 1) = true ∧
    matOK codeRA (CA.T CA.r0) = true ∧ matOK codeRB (CB.T CB.r0) = true ∧
    (List.range 4).all (fun k => matOK (sylCodes.getD k 0) (SH.G k)) = true ∧
    Nat.beq (SH.T 0) (pidn 341 9) = true ∧ CA.N = 165 ∧ CB.N = 2970 ∧ SH.N = 1024 ∧
    CA.ng = 2 ∧ CB.ng = 2 ∧ SH.ng = 4 ∧ CA.r0 < 165 ∧ CB.r0 < 2970 := by
  decide +kernel

@[expose] noncomputable def invol (t : Nat) : Bool :=
  ((List.range 341).all fun i => Nat.beq (pg 9 (mask 9) t (pg 9 (mask 9) t i)) i) &&
    !Nat.beq t (pidn 341 9)

@[expose] noncomputable def inClasses (a b : Bool) (t : Nat) : Bool :=
  (a && (List.range 165).any fun j => Nat.beq (CA.T j) t) ||
    (b && (List.range 2970).any fun j => Nat.beq (CB.T j) t)

@[expose] noncomputable def coverK (a b : Bool) (m : Nat) : Bool :=
  (List.range m).all fun i => !invol (SH.T i) || inClasses a b (SH.T i)

theorem cover : coverK true true 1024 = true := by decide +kernel

theorem cover_neg : (!coverK true false 1024 && !coverK false true 1024) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U52

end
