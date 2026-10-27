module

public import Certificates.Kernel.L34Cov.LiftNormChecks
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.PresentationLetters
meta import Certificates.Data.Kernel.L34Cov.ABTabs

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34Cov.AB CFSG.KC.L34Cov.abLetTabs 6

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W
open CFSG.PSL3Four.Native CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.Certificates.CosetEnumeration
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def abK (w : List (Fin 2 × Bool)) : Nat :=
  pword AB (w.map letterCode) (pidn 42 6)

@[expose] noncomputable def r4K : Nat := pcomp 42 6 (mask 6) (GT 4) (GT 5)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def oneK (x : Nat) : Bool := Nat.beq x (pidn 42 6)

@[expose] noncomputable def invCK (W ρ : Nat) : Bool :=
  oneK (pc W W) && !oneK W && Nat.beq (pc W ρ) (pc ρ W)

theorem ch22201t_ab :
    (Nat.beq (pword (gS GT) wa (pidn 42 6)) (AB 0) && Nat.beq (pword (gS GT) wb (pidn 42 6)) (AB 2) &&
      canonK 42 6 (mask 6) 252 (AB 1) && canonK 42 6 (mask 6) 252 (AB 3) &&
      oneK (pc (AB 0) (AB 1)) && oneK (pc (AB 2) (AB 3))) = true := by
  decide +kernel

theorem ch22201t_rel :
    (rels.all (fun r => oneK (abK r)) && coverWs.all (fun r => oneK (abK r)) &&
      oneK (abK zOne) && oneK (abK zTwo) && oneK (abK zThree) && !oneK (AB 2)) = true := by
  decide +kernel

theorem ch22201t_gen :
    (Nat.beq (abK (genABWords.getD 0 [])) (GT 0) && Nat.beq (abK (genABWords.getD 1 [])) (GT 1) &&
      Nat.beq (abK (genABWords.getD 2 [])) (GT 2)) = true := by
  decide +kernel

theorem ch22201t_aut :
    (Nat.beq (abK uAU) (cjK r4K (AB 0)) && Nat.beq (abK uBU) (cjK r4K (AB 2)) &&
      Nat.beq (abK uAF) (cjK (GT 4) (AB 0)) && Nat.beq (abK uBF) (cjK (GT 4) (AB 2)) &&
      Nat.beq (abK uAG) (cjK (GT 5) (AB 0)) && Nat.beq (abK uBG) (cjK (GT 5) (AB 2))) = true := by
  decide +kernel

theorem ch22201t_tw : allN 64 (fun k => Nat.beq (abK (tw k)) (tgK GT k) &&
    CertificateChecks.KernelLC.L34Para.memK 64 CertificateChecks.KernelLC.L34PT.T (tgK GT k)) =
    true := by
  decide +kernel

theorem ch22201t_dist :
    allN 64 (fun k => allN k fun l => !Nat.beq (tgK GT k) (tgK GT l)) = true := by
  decide +kernel

theorem ch22201t_inv : allN 64 (fun k => oneK (pc (tgK GT k) (tgK GT k)) ==
    (k == 0 || (sqData.map (·.1)).contains k)) = true := by
  decide +kernel

theorem ch22201t_r4 : allN 64 (fun k => CertificateChecks.KernelLC.L34Para.memK 64
    CertificateChecks.KernelLC.L34PT.T (cjK r4K (tgK GT k))) = true := by
  decide +kernel

theorem ch22201t_q8 : allN 64 (fun k => Nat.beq (pc (tgK GT k) r4K) (pc r4K (tgK GT k)) ==
    q8Idx.contains k) = true := by
  decide +kernel

theorem ch22201t_c8 : Nat.beq (countBelow 64 fun k => oneK (pc (tgK GT k) (cjK r4K (tgK GT k))))
    8 = true := by
  decide +kernel

theorem ch22201t_wit : (invCK (abK witnessF) (GT 4) && invCK (abK witnessG) (GT 5) &&
    invCK (abK witnessU) r4K) = true := by
  decide +kernel

theorem ch22201t_neg1 : (!invCK (abK witnessG) (GT 4)) = true := by decide +kernel

theorem ch22201t_neg2 : (!Nat.beq (abK (tw 2)) (tgK GT 1)) = true := by decide +kernel

theorem ch22201t_neg3 : (!(oneK (pc (tgK GT 1) (tgK GT 1)) == (1 == 0 || false))) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
