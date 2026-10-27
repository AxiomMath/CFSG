module

public import Certificates.Kernel.Misc.Coset.Q3Act.K0
public import Certificates.Kernel.Misc.Coset.Q3Act.K1
public import Certificates.Kernel.Misc.Coset.Q3Act.K2
public import Certificates.Kernel.Misc.Coset.Q3Act.K3
public import Certificates.Kernel.Misc.Coset.Q3Act.K4
public import Certificates.Kernel.Misc.Coset.Q3Act.K5
public import Certificates.Kernel.Misc.Coset.Q3Act.K6
public import Certificates.Kernel.Misc.Coset.Q3Act.K7
public import Certificates.Kernel.Misc.Coset.Q3Act.K8
public import Certificates.Kernel.Misc.Coset.Q3Act.K9
public import Certificates.Kernel.Misc.Coset.Q3Act.K10
public import Certificates.Kernel.Misc.Coset.Q3Act.K11
public import Certificates.Kernel.Misc.Coset.Q3Act.K12
public import Certificates.Kernel.Misc.Coset.Q3Act.K13
public import Certificates.Kernel.Misc.Coset.Q3Act.K14
public import Certificates.Kernel.Misc.Coset.Q3Act.K15
public import Certificates.Kernel.Misc.Coset.Q3Act.K16
public import Certificates.Kernel.Misc.Coset.Q3Act.K17
public import Certificates.Kernel.Misc.Coset.Q3Act.K18
public import Certificates.Kernel.Misc.Coset.Q3Act.K19
public import Certificates.Kernel.Misc.Coset.Q3Act.K20
public import Certificates.Kernel.Misc.Coset.Q3Act.Sym
public import CFSG.Certificates.Kernel.Misc.Coset.CovActSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KAct.Q3

open CFSG.KC.MiscCoset.Act CFSG.KC.MiscCoset.CovAct
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

#kc_forall_tree blkAll (fun k => blk k = true) 4263 CFSG.KAct.Q3.blk

theorem cpOK_all : ∀ p < 306936, cpOK A 3 306936 11 25 mac chk p = true := by
  intro p hp
  have hlt : p / 72 < 4263 := by omega
  have hk := blkAll (p / 72) hlt
  unfold blk at hk
  have h1 : Nat.mul (p / 72) 72 ≤ p := Nat.div_mul_le_self p 72
  have h2 : p < Nat.mul (p / 72) 72 + 72 := by
    have := Nat.lt_div_mul_add (a := p) (b := 72) (by norm_num)
    exact this
  exact allR_spec hk p h1 h2

theorem three_dvd_orderOf_zeta :
    3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk}
      (FreeGroup.mk (zetaWord 10))) := by
  rw [wsQ_eq]
  exact dvd_orderOf_of_covAct (wsQN CFSG.KD.OrdFi24p.rels) Nat.prime_three (by norm_num) cpOK_all
    hint sym (zeta 10) (by decide) (by decide)

end CFSG.KAct.Q3
