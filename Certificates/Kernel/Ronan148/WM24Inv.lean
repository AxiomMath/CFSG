module

public import Certificates.Kernel.Tc.M24
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WM24Inputs
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.RankThree.PartTwo.Sec14.Ronan148WM24Inputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

namespace CertificateChecks.KernelRonan148.WM24Inv

meta def invM : Array (Array Nat) := CFSG.RankThree.PartTwo.Sec14.Ronan148W.invArrs ()

end CertificateChecks.KernelRonan148.WM24Inv

public section

#kmisc_packarrs CertificateChecks.KernelRonan148.WM24Inv.QP
  CertificateChecks.KernelRonan148.WM24Inv.invM 5

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRonan148.WM24Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CertificateChecks.KernelTc.M24
open CFSG.RankThree.PartTwo.Sec14.Ronan148W

@[expose] noncomputable def pcj (q p : Nat) : Nat :=
  pcomp 24 5 (mask 5) q (pcomp 24 5 (mask 5) p (pinvS 24 5 (mask 5) q))

@[expose] noncomputable def ppw (p e : Nat) : Nat := ppow 24 5 (mask 5) (pidn 24 5) p e

@[expose] noncomputable def invK (X : Nat) (Q : Nat → Nat) (N : Nat) (T : Nat → Nat) : Bool :=
  permB 24 5 X &&
    CFSG.KC.LQT.P.allN 6 (fun l => permB 24 5 (Q l) &&
      Nat.beq (pcj (Q l) X) (pinvS 24 5 (mask 5) X)) &&
    CFSG.KC.LQT.P.allN N (fun k => !(Nat.beq (ppw (T k) 3) (pidn 24 5)) ||
      CFSG.KC.LQT.P.anyN 6 (fun l => CFSG.KC.LQT.P.anyN 3 (fun i => CFSG.KC.LQT.P.anyN 3
        (fun j => Nat.beq (pcj (Q l) (T k)) (pcomp 24 5 (mask 5) (ppw X i) (ppw (T k) j))))))

theorem bQ : ∀ l < 6, arrBind (invArrs ())[l]! 24 5 (QP l) = true := by
  intro l hl
  interval_cases l <;> quickRfl

theorem kInv : invK (MS 10) QP EC.N EC.T = true := by
  quickRfl

theorem kInvNeg : (!invK (MS 10) (fun _ => MS 10) EC.N EC.T) = true := by
  quickRfl

end CertificateChecks.KernelRonan148.WM24Inv

end
