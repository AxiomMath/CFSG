module

public import Certificates.Kernel.SuzA17321.Chain
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.Kernel.Misc.PermWit
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzA17321

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.HeDih
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzA CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

@[expose] noncomputable def XP : Nat := (reb xATuple).1

@[expose] noncomputable def UP : Nat := (reb uTuple).1

@[expose] noncomputable def VP : Nat := (reb vTuple).1

@[expose] noncomputable def TP : Nat := (reb tTuple).1

@[expose] noncomputable def AB (k : Nat) : Nat := SAC.S k

@[expose] noncomputable def modX (e : Nat) : Bool :=
  Nat.beq e (pidn 1782 11) || Nat.beq e XP || Nat.beq e (pcomp 1782 11 (mask 11) XP XP)

@[expose] noncomputable def siftPK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (1782 * 11)) 0 &&
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) &&
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G

@[expose] noncomputable def siftCK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (1782 * 11)) 0 &&
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) &&
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SAC.LR SAC.TRI SAC.BP 6 0 G

@[expose] noncomputable def fixXK (i : Nat) : Nat :=
  CFSG.KC.PermWit.cntK 1782 (fun q => Nat.beq (pg 11 (mask 11) XP q) q &&
    Nat.blt (rpos 11 (mask 11) (1782 * 11) (SuzC.LR i) q) (rcnt (SuzC.LR i)))

theorem rbAll : (reb xATuple).2.2 = true ∧ (reb uTuple).2.2 = true ∧ (reb vTuple).2.2 = true ∧
    (reb tTuple).2.2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem pAll : permB 1782 11 XP = true ∧ permB 1782 11 UP = true ∧ permB 1782 11 VP = true ∧
    permB 1782 11 TP = true ∧ permB 1782 11 (AB 0) = true ∧ permB 1782 11 (AB 1) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem xS : Nat.beq (SAC.S 2) XP = true := by quickRfl

theorem siftP : siftPK (AB 0) = true ∧ siftPK (AB 1) = true ∧ siftPK TP = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftC : siftCK UP = true ∧ siftCK VP = true := ⟨by quickRfl, by quickRfl⟩

theorem commX : Nat.beq (cm 1782 11 (AB 0) XP) (cm 1782 11 XP (AB 0)) = true ∧
    Nat.beq (cm 1782 11 (AB 1) XP) (cm 1782 11 XP (AB 1)) = true := ⟨by quickRfl, by quickRfl⟩

theorem relX : CFSG.LieType.Multipliers.U43.rels.all (fun wd => modX (evalWK 1782 11 AB wd)) =
    true := by
  decide +kernel

theorem commUV : Nat.beq (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) VP UP)
    (pcomp 1782 11 (mask 11) (pinvS 1782 11 (mask 11) VP) (pinvS 1782 11 (mask 11) UP))) XP =
      true := by
  quickRfl

theorem conjT : Nat.beq (pcomp 1782 11 (mask 11) TP (pcomp 1782 11 (mask 11) XP
    (pinvS 1782 11 (mask 11) TP))) (pcomp 1782 11 (mask 11) XP XP) = true := by
  quickRfl

theorem fixB : allN 5 (fun i => Nat.beq (pg 11 (mask 11) XP i) i) = true := by quickRfl

theorem fixL : Nat.beq (fixXK 0) 162 = true ∧ Nat.beq (fixXK 1) 56 = true ∧
    Nat.beq (fixXK 2) 10 = true ∧ Nat.beq (fixXK 3) 9 = true ∧ Nat.beq (fixXK 4) 8 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem cnt5 : Nat.beq (CFSG.KC.PermWit.cntK 1782 (fun q =>
    Nat.blt (rpos 11 (mask 11) (1782 * 11) (SuzC.LR 5) q) (rcnt (SuzC.LR 5)))) 3 = true := by
  quickRfl

end CertificateChecks.KernelSuzA17321

end
