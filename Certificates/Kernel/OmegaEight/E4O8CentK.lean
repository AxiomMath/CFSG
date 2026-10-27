module

public import Certificates.Kernel.OmegaEight.E4O8CentData
public import Certificates.Kernel.OmegaEight.E4O8NbrK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E4C

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8

@[expose] noncomputable def e4Comm (a b : Nat) : Bool := Nat.beq (pc a b) (pc b a)

@[expose] noncomputable def e4Lets (k : Nat) (W : List (List Nat)) : Bool :=
  W.all fun w => allL (fun c => Nat.blt c k) w

theorem ch550106sz : szOK 360 9 = true := by quickRfl

theorem ch550106pm : bAnd(allN 6 (fun k => permB 360 9 (g0K k)), bAnd(allN 6 (fun k => permB 360 9 (g1K k)),
    bAnd(allN 6 (fun k => permB 360 9 (g2K k)), bAnd(allN 4 (fun k => permB 360 9 (g3K k)),
    bAnd(permB 360 9 C, bAnd(permB 360 9 (mainK 0), bAnd(permB 360 9 e4U, permB 360 9 om0V))))))) =
      true := by
  quickRfl

theorem ch550106x : bAnd(classK 360 9 AP.S AP.S 8 (mainK 0) RX, Nat.beq RX.length 1575) = true := by
  quickRfl

theorem ch550106g0 : bAnd(Nat.beq (g0K 0) (wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [1])),
    bAnd(Nat.beq (g0K 1) (wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [2])),
    bAnd(Nat.beq (g0K 2) (wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [3])),
    bAnd(Nat.beq G0.length 6, allN 6 (fun k => e4Comm (g0K k) (mainK 0)))))) = true := by
  quickRfl

theorem ch550106l0 : bAnd(stabLowK 360 9 g0K 6 L0,
    Nat.beq (L0.map fun lv => lv.2.2.2.length).prod 110592) = true := by
  quickRfl

theorem ch550106u : bAnd(classK 360 9 g0K gi0K 6 e4U RU, Nat.beq RU.length 24) = true := by
  quickRfl

theorem ch550106g1 : bAnd(Nat.beq G1.length 6, bAnd(Nat.beq W1.length 6, bAnd(e4Lets 6 W1,
    allN 6 (fun k => bAnd(Nat.beq (g1K k) (wordK 360 9 g0K (W1.getD k [])),
      e4Comm (g1K k) e4U))))) = true := by
  quickRfl

theorem ch550106l1 : bAnd(stabLowK 360 9 g1K 6 L1,
    Nat.beq (L1.map fun lv => lv.2.2.2.length).prod 4608) = true := by
  quickRfl

theorem ch550106v : bAnd(classK 360 9 g1K gi1K 6 om0V RV, Nat.beq RV.length 4) = true := by
  quickRfl

theorem ch550106g2 : bAnd(Nat.beq G2.length 6, bAnd(Nat.beq W2.length 6, bAnd(e4Lets 6 W2,
    allN 6 (fun k => bAnd(Nat.beq (g2K k) (wordK 360 9 g1K (W2.getD k [])),
      bAnd(e4Comm (g2K k) e4U, e4Comm (g2K k) om0V)))))) = true := by
  quickRfl

theorem ch550106l2 : bAnd(stabLowK 360 9 g2K 6 L2,
    Nat.beq (L2.map fun lv => lv.2.2.2.length).prod 1152) = true := by
  quickRfl

theorem ch550106c : bAnd(Nat.beq C (wordK 360 9 g0K WC), bAnd(e4Lets 6 [WC],
    bAnd(Nat.beq (pc C (pc C C)) pid, bAnd(classK 360 9 g2K gi2K 6 C RC,
      Nat.beq RC.length 64)))) = true := by
  quickRfl

theorem ch550106g3 : bAnd(Nat.beq G3.length 4, bAnd(Nat.beq W3.length 4, bAnd(e4Lets 6 W3,
    bAnd(allN 4 (fun k => bAnd(Nat.beq (g3K k) (wordK 360 9 g2K (W3.getD k [])), e4Comm (g3K k) C)),
    bAnd(orbRecK (fun k y => pcomp 360 9 (mask 9) (g3K k) y) 4 pid R3,
      Nat.beq R3.length 18))))) = true := by
  quickRfl

theorem ch550106i : allL (fun r => bIf(Nat.beq (pc r r) pid,
    bIf(Nat.beq r pid, true, Nat.beq r (mainK 0)), true)) (R3.map Prod.fst) = true := by
  quickRfl

end CertificateChecks.KernelO8.E4C

end
