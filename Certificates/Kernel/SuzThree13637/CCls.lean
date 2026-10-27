module

public import Certificates.Kernel.SuzThree13637.ClsData
public import Certificates.Kernel.SuzThree13637.CEnum
public import Certificates.Data.Kernel.Spor.ClsK
public import Certificates.Data.Kernel.Spor.PSearch
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.ClsK CertificateChecks.KernelSpor

@[expose] def ySrc : List Nat := [0, 0, 1, 3, 3, 5]

@[expose] noncomputable def yYs : List Nat := [CD.I, CD.Y, CD.Y, CD.I, CD.Y2, CD.I]

@[expose] noncomputable def cgenOK (k : Nat) : Bool :=
  strictB (CE.G k) fun G =>
    bAnd(allN 1782 (fun p => Nat.beq (pg 11 (mask 11) G (pg 11 (mask 11) CD.Y p))
      (pg 11 (mask 11) CD.Y (pg 11 (mask 11) G p))),
    bAnd(Nat.beq (Nat.shiftRight G (1782 * 11)) 0,
    bAnd(allN 1782 (fun i => Nat.blt (pg 11 (mask 11) G i) 1782),
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G)))

theorem cd_ok : (Nat.beq CD.I (pidn 1782 11) && Nat.beq CD.Y (CE.G 0) &&
    Nat.beq (pcomp 1782 11 (mask 11) CD.Y CD.Y) CD.Y2) = true := by
  quickRfl

theorem cgen_ok : ∀ k < 3, cgenOK k = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem csrc_ok : srcOK 11 (mask 11) SuzC.BP 6 ySrc yYs = true := by quickRfl

theorem csearch_ok : Nat.beq (pcnt 1782 11 (mask 11) (1782 * 11) SuzC.LR SuzC.TR SuzC.TRI SuzC.BP 6
    ySrc yYs [CD.Y]) 3240 = true := by
  quickRfl

theorem cls_ok : clsK 11 (mask 11) CD.I 3240 CE.T [0, 1, 2, 3] CD.reps CD.tag 41 = true := by
  quickRfl

end CFSG.KD.SuzThree13637

end
