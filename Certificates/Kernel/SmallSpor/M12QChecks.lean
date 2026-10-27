module

public import Certificates.Kernel.SmallSpor.M12QData
public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Data.Kernel.ListBridge
public import Certificates.Data.Kernel.SporSch.MathieuOC
public import CFSG.Certificates.Kernel.Spor.BindList
public import Certificates.Data.ExitTwoM12
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M12Q

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge CFSG.KS.SporSch.MOC
open CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12 CertificateChecks.KernelSmallSpor.M12
open CertificateChecks.KernelSporSch
open CFSG.KLie.CT (notB)

@[expose] noncomputable def cj (g x : Nat) : Nat :=
  pcomp 12 4 (mask 4) (pcomp 12 4 (mask 4) g x) (pinvS 12 4 (mask 4) g)

@[expose] noncomputable def wA (wd : List Int) : Nat :=
  abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1) wd

@[expose] noncomputable def wB (wd : List Int) : Nat :=
  abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (WV 0) (WV 1) wd

@[expose] noncomputable def q8K (Q : Nat → Nat) : Bool :=
  bAnd(Nat.beq (Q 0) (pidn 12 4), bAnd(Nat.beq (Q 2) (pcomp 12 4 (mask 4) (Q 1) (Q 1)),
    bAnd(Nat.beq (Q 3) (pcomp 12 4 (mask 4) (Q 2) (Q 1)),
      bAnd(Nat.beq (Q 5) (pcomp 12 4 (mask 4) (Q 1) (Q 4)),
        bAnd(Nat.beq (Q 6) (pcomp 12 4 (mask 4) (Q 2) (Q 4)),
          Nat.beq (Q 7) (pcomp 12 4 (mask 4) (Q 3) (Q 4)))))))

@[expose] def tBp : List Nat := [5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6]

theorem tBp_eq : tBp = CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m12bp := by
  decide

theorem bindBp : bindListK 12 4 (WV 0) tBp = true ∧
    permOK 12 4 (mask 4) (12 * 4) (WV 0) (WV 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem words : abOK wI0 = true ∧ abOK wJ0 = true ∧ abOK wI1 = true ∧ abOK wJ1 = true ∧
    abOK wG = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem binds : Nat.beq (Q0 1) (wA wI0) = true ∧ Nat.beq (Q0 4) (wA wJ0) = true ∧
    Nat.beq (Q1 1) (wA wI1) = true ∧ Nat.beq (Q1 4) (wA wJ1) = true ∧
    Nat.beq (B0 1) (wB wI0) = true ∧ Nat.beq (B0 4) (wB wJ0) = true ∧
    Nat.beq (B1 1) (wB wI1) = true ∧ Nat.beq (B1 4) (wB wJ1) = true ∧
    Nat.beq (WV 2) (wA wG) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl, by quickRfl⟩

theorem shape : q8K Q0 = true ∧ q8K Q1 = true ∧ q8K B0 = true ∧ q8K B1 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem canon : allN 8 (fun k => canonK 12 4 (mask 4) (12 * 4) (Q0 k)) = true ∧
    allN 8 (fun k => canonK 12 4 (mask 4) (12 * 4) (Q1 k)) = true ∧
    allN 8 (fun k => canonK 12 4 (mask 4) (12 * 4) (B0 k)) = true ∧
    allN 8 (fun k => canonK 12 4 (mask 4) (12 * 4) (B1 k)) = true ∧
    canonK 12 4 (mask 4) (12 * 4) M12OC.R0 = true ∧
    canonK 12 4 (mask 4) (12 * 4) (WV 2) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem memC : allN 8 (fun k => inK EK1.N EK1.T (Q0 k)) = true ∧
    allN 8 (fun k => inK EK1.N EK1.T (Q1 k)) = true := ⟨by quickRfl, by quickRfl⟩

theorem closed : allN 8 (fun a => allN 8 fun b => inK 8 Q0 (pcomp 12 4 (mask 4) (Q0 a) (Q0 b))) =
      true ∧
    allN 8 (fun a => allN 8 fun b => inK 8 Q1 (pcomp 12 4 (mask 4) (Q1 a) (Q1 b))) = true ∧
    allN 8 (fun a => inK 8 Q0 (pinvS 12 4 (mask 4) (Q0 a))) = true ∧
    allN 8 (fun a => inK 8 Q1 (pinvS 12 4 (mask 4) (Q1 a))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem rootsAll : allN EK1.N (fun i => bIf(Nat.beq (pcomp 12 4 (mask 4) (EK1.T i) (EK1.T i))
    M12OC.R0, inK (NR 0) RI i, true)) = true := by quickRfl

theorem rootsPair : allN (NR 0) (fun k => strictB (EK1.T (RI k)) fun x =>
    bAnd(bIf(inK 8 Q0 x, true, inK 8 Q1 x),
      allN (NR 0) fun l => strictB (EK1.T (RI l)) fun y =>
        bIf(Nat.beq (pcomp 12 4 (mask 4) x y) (pcomp 12 4 (mask 4) y x), true,
          bIf(bAnd(inK 8 Q0 x, inK 8 Q0 y), true, bAnd(inK 8 Q1 x, inK 8 Q1 y))))) = true := by
  quickRfl

theorem norm : allN EK1.N (fun i => allN 8 fun a =>
    bAnd(inK 8 Q0 (cj (EK1.T i) (Q0 a)), inK 8 Q1 (cj (EK1.T i) (Q1 a)))) = true := by quickRfl

theorem beta : allN 8 (fun k => inK 8 Q1 (B0 k)) = true ∧ allN 8 (fun k => inK 8 Q0 (B1 k)) =
    true := ⟨by quickRfl, by quickRfl⟩

theorem wit : notB (Nat.beq (cj (WV 2) (Q1 7)) (pidn 12 4)) = true ∧
    notB (Nat.beq (pcomp 12 4 (mask 4) (cj (WV 2) (Q1 7)) (cj (WV 2) (Q1 7))) (pidn 12 4)) =
      true ∧
    allN 8 (fun a => inK 8 Q0 (cj (cj (WV 2) (Q1 7)) (Q0 a))) = true ∧
    notB (allN 8 fun a => inK 8 Q0 (cj (cj (WV 2) (Q1 6)) (Q0 a))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem meet : allN 8 (fun k => bIf(inK 8 Q1 (Q0 k),
      bIf(Nat.beq (Q0 k) (pidn 12 4), true, Nat.beq (Q0 k) M12OC.R0), true)) = true ∧
    Nat.beq (Q0 2) M12OC.R0 = true ∧ Nat.beq (Q1 2) M12OC.R0 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSmallSpor.M12Q

end
