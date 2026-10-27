module

public import Certificates.Kernel.LyFive.Data
public import Certificates.Kernel.SporSch.Ly.SevA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyFive

open CFSG.KC.LyG2 CFSG.KC.Enum CertificateChecks.KernelLyFive.D

theorem data : dataChk CC TT = true := by quickRfl

theorem a0 : lvlChk CC TT [] a0_fixed a0_b a0_ins = true := by quickRfl
theorem a1 : lvlChk CC TT [] a1_fixed a1_b a1_ins = true := by quickRfl
theorem a2 : lvlChk CC TT [] a2_fixed a2_b a2_ins = true := by quickRfl
theorem x0 : lvlChk CC TT [packCols RX] x0_fixed x0_b x0_ins = true := by quickRfl
theorem x1 : lvlChk CC TT [packCols RX] x1_fixed x1_b x1_ins = true := by quickRfl
theorem y3 : lvlChk CC TT [packCols RY3] y3_fixed y3_b y3_ins = true := by quickRfl
theorem y1 : lvlChk CC TT [packCols RY1] y1_fixed y1_b y1_ins = true := by quickRfl

theorem a2f : finChk CC [] a2_fixed a2_b a2_ins a2_ui = true := by quickRfl
theorem x1f : finChk CC [packCols RX] x1_fixed x1_b x1_ins x1_ui = true := by quickRfl
theorem y3f : finChk CC [packCols RY3] y3_fixed y3_b y3_ins y3_ui = true := by quickRfl
theorem y1f : finChk CC [packCols RY1] y1_fixed y1_b y1_ins y1_ui = true := by quickRfl

theorem fixed : bAnd(Nat.beq (lenL a0_fixed) 0, bAnd(Nat.beq (lenL x0_fixed) 0,
    bAnd(Nat.beq (lenL y3_fixed) 0, Nat.beq (lenL y1_fixed) 0))) = true := by quickRfl

theorem chainA : bAnd(Nat.beq (lenL a1_fixed) 1, bAnd(Nat.beq (getL a1_fixed 0) a0_b,
    bAnd(Nat.beq (lenL a2_fixed) 2, bAnd(Nat.beq (getL a2_fixed 0) a0_b,
    Nat.beq (getL a2_fixed 1) a1_b)))) = true := by quickRfl

theorem chainX : bAnd(Nat.beq (lenL x1_fixed) 1, Nat.beq (getL x1_fixed 0) x0_b) = true := by quickRfl

theorem roots : bAnd(lt5L RX, bAnd(lt5L RY3, bAnd(lt5L RY1, bAnd(Nat.beq (lenL RX) 49,
    bAnd(Nat.beq (lenL RY3) 49, Nat.beq (lenL RY1) 49))))) = true := by quickRfl

theorem gens : allN 5 (fun j => bAnd(lt5L (CertificateChecks.KernelSporSch.LySv.HP[j]!.1.toList),
    bAnd(Nat.beq (lenL (CertificateChecks.KernelSporSch.LySv.HP[j]!.1.toList)) 49,
      autChk CC (packCols (CertificateChecks.KernelSporSch.LySv.HP[j]!.1.toList))))) = true := by
  quickRfl

theorem witsLen : Nat.beq (lenA y3_wit) 3750 = true := by quickRfl

theorem witsInc : keysInc y3_b y3_wit = true := by quickRfl

end CertificateChecks.KernelLyFive

end
