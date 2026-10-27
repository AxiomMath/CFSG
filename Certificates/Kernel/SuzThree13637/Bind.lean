module

public import Certificates.Kernel.SuzThree13637.HypData
public import Certificates.Kernel.SuzThree13637.BindSrc
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Spor.HypK
public import Certificates.Data.Kernel.PGrp
public meta import Certificates.Kernel.SuzThree13637.BindSrc
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_perm CFSG.KD.SuzThree13637.Q0 11 CFSG.KD.SuzThree13637.qA0

#ks_perm CFSG.KD.SuzThree13637.Q1 11 CFSG.KD.SuzThree13637.qA1

#ks_perm CFSG.KD.SuzThree13637.Q2 11 CFSG.KD.SuzThree13637.qA2

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.HypK CFSG.KC.PGrp
  CFSG.KC.Misc.ArrEnum CertificateChecks.KernelSpor
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81

@[expose] noncomputable def bG (l : Nat) : Nat := nthN [Suz2306.B0, Suz2306.B1] l

@[expose] noncomputable def qG (l : Nat) : Nat := nthN [Q0, Q1, Q2] l

theorem bind_perm : (permB 1782 11 Suz2306.B0 && permB 1782 11 Suz2306.B1 && permB 1782 11 Q0 &&
    permB 1782 11 Q1 && permB 1782 11 Q2) = true := by
  quickRfl

theorem bind_letters : (suzE81.qW.toList.all fun w => w.all fun l => decide (l < 2)) = true ∧
    ((suzE81.dW[0]!).toList.all fun w => w.all fun l => decide (l < 3)) = true ∧
    suzE81.qW.size = 3 ∧ (suzE81.dW[0]!).size = 5 := by
  simp only [suzE81, Array.toList_map, Array.size_map]
  decide +kernel

theorem bind_q : suzE81.qW.toList.map (posWordK 1782 11 bG) = [Q0, Q1, Q2] := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem bind_d : (suzE81.dW[0]!).toList.map (posWordK 1782 11 qG) = F.D := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem bind_nb : allN 2 (fun i => withReb 1782 11 SuzC.LR SuzC.TR SuzC.TRI (nthL F.nb i)
    fun q ok => bAnd(ok, Nat.beq q (qG (Nat.succ i)))) = true := by
  quickRfl

end CFSG.KD.SuzThree13637

end
