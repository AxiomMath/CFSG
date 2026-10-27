module

public import Certificates.Kernel.Misc.Perm.HS100.OData
public import Certificates.Kernel.Misc.Perm.HS100.S0Checks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.O

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit
open CFSG.KC.Misc.ArrEnum (permB)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (cK)
open CFSG.EvenSporadicStandard.HSStd

@[expose] noncomputable def KK (i : Nat) : Nat := pg 8 (mask 8) (KX.F 0) i

@[expose] noncomputable def JJ (i : Nat) : Nat := pg 12 (mask 12) (JX.F 0) i

@[expose] noncomputable def p5K (p : Nat) : Nat :=
  pcomp 100 7 (mask 7) p (pcomp 100 7 (mask 7) p (pcomp 100 7 (mask 7) p (pcomp 100 7 (mask 7) p p)))

@[expose] noncomputable def CC (k : Nat) : Nat := OS.T s5fRep[k]!

@[expose] noncomputable def TK (i : Nat) : Nat := pcomp 100 7 (mask 7) (OX.F (7 + i)) (OX.F (8 + i))

@[expose] noncomputable def GK (k : Nat) : Nat :=
  if k < 6 then TK k else
    pcomp 100 7 (mask 7) (OX.F 6) (pcomp 100 7 (mask 7) (TK (k - 6)) (pinvS 100 7 (mask 7) (OX.F 6)))

@[expose] noncomputable def LK (l : Nat) : Nat :=
  if l < 12 then GK l else pinvS 100 7 (mask 7) (GK (l - 12))

@[expose] noncomputable def evalK (w : List Nat) : Nat :=
  w.foldl (fun acc l => pcomp 100 7 (mask 7) acc (LK l)) (pidn 100 7)

@[expose] noncomputable def invPt (i : Nat) : Bool :=
  strictB (OS.T i) fun x =>
    !(Nat.beq (pcomp 100 7 (mask 7) x x) (pidn 100 7)) || Nat.beq x (pidn 100 7) ||
      (Nat.blt (KK i) 19 && Nat.blt (JJ i) 1024 &&
        Nat.beq (pcomp 100 7 (mask 7) (OS.T (JJ i)) (CC (KK i))) (pcomp 100 7 (mask 7) x (OS.T (JJ i))))

theorem perms : (allN 16 (fun k => permB 100 7 (OX.F k)) && allN 19 (fun k => permB 100 7 (FX.F k)) &&
    allN 24 (fun l => permB 100 7 (LK l))) = true := by quickRfl

theorem fsift : allN 19 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (FX.F k)) = true := by quickRfl

theorem nums : (Nat.beq OS.ng 4 && Nat.beq OS.N 1024 && allN 4 (fun k => Nat.beq (OS.G k) (OX.F k))) =
    true := by quickRfl

theorem keys : keysSK 100 7 s5Keys OS.N OS.T ((List.range 1024).map OSK) = true := by quickRfl

theorem reps : allN 19 (fun k => Nat.blt s5fRep[k]! 1024) = true := by quickRfl

theorem fives : allN 19 (fun k =>
    Nat.beq (p5K (FX.F k)) (pidn 100 7) &&
      !(Nat.beq (FX.F k) (pidn 100 7)) && cK (FX.F k) (CC k)) = true := by quickRfl

theorem invs : allN 1024 invPt = true := by quickRfl

theorem words : (Nat.beq (evalK s5fWA) (HX.F 0) && Nat.beq (evalK s5fWB) (HX.F 1)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.HS100.O

end
