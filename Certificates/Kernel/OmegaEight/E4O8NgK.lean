module

public import Certificates.Kernel.OmegaEight.E4O8CentData
public import Certificates.Kernel.OmegaEight.E4O8NgData
public import Certificates.Kernel.OmegaEight.E4O8NbrK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E4C

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8

@[expose] def ngY1W : List Int := CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [-1, 3, -2, -3, 1, -2]

@[expose] def ngY2W : List Int :=
  CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [-3, -2, -1, -2, -3, -2, -2, 1]

@[expose] noncomputable def ngComm (a b : Nat) : Bool := Nat.beq (pc a b) (pc b a)

theorem ch55116pm : bAnd(allN 6 (fun k => permB 360 9 (g4K k)),
    bAnd(permB 360 9 Y1, permB 360 9 Y2)) = true := by
  quickRfl

theorem ch55116y : bAnd(lettersK 17 ngY1W, bAnd(lettersK 17 ngY2W, bAnd(Nat.beq Y1 (wO ngY1W),
    bAnd(Nat.beq Y2 (wO ngY2W), bAnd(Nat.beq (pc Y1 (pc Y1 Y1)) pid,
    bAnd(Nat.beq (pc Y2 (pc Y2 Y2)) pid, bAnd(ngComm Y1 e4U, bAnd(ngComm Y1 om0V,
    bAnd(ngComm Y2 e4U, ngComm Y2 om0V))))))))) = true := by
  quickRfl

theorem ch55116c1 : bAnd(classK 360 9 g0K gi0K 6 Y1 RY1, Nat.beq RY1.length 512) = true := by
  quickRfl

theorem ch55116g4 : bAnd(Nat.beq G4.length 6, bAnd(Nat.beq W4.length 6,
    bAnd(W4.all (fun w => allL (fun c => Nat.blt c 6) w),
    allN 6 (fun k => bAnd(Nat.beq (g4K k) (wordK 360 9 g0K (W4.getD k [])),
      ngComm (g4K k) Y1))))) = true := by
  quickRfl

theorem ch55116l4 : bAnd(stabLowK 360 9 g4K 6 L4,
    Nat.beq (L4.map fun lv => lv.2.2.2.length).prod 216) = true := by
  quickRfl

theorem ch55116c2 : bAnd(classK 360 9 g4K gi4K 6 Y2 RY2, Nat.beq RY2.length 27) = true := by
  quickRfl

end CertificateChecks.KernelO8.E4C

end
