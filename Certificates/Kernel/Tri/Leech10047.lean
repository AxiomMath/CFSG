module

public import Certificates.Kernel.Tri.LeechShort
public import Certificates.Kernel.Tri.LeechTabs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.Short.AxisAction
public import CFSG.Monster.B.Short.OrbitCertBase
public import CFSG.Monster.B.Short.OrbitSpec

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLeech

open CFSG.KLie.CT CFSG.KC.Leech CFSG.Monster.Tri.Leech CertificateChecks.Short3014

@[expose] noncomputable def I3 : Nat → Nat := getK leechIdx3.toList
@[expose] noncomputable def P3 : Nat → Nat := getK leechPar3.toList
@[expose] noncomputable def L3 : Nat → Nat := getK leechLev3.toList
@[expose] noncomputable def I4 : Nat → Nat := getK leechIdx4.toList
@[expose] noncomputable def P4 : Nat → Nat := getK leechPar4.toList
@[expose] noncomputable def L4 : Nat → Nat := getK leechLev4.toList

theorem sz3 : leechIdx3.size = 275 := by decide
theorem sz4 : leechIdx4.size = 88 := by decide

theorem s3 : allN 275 (sortedAt 275 I3) = true := by quickRfl
theorem v3 : allN 275 (muVsAt memS 1 I3) = true := by quickRfl
theorem t3 : allN 275 (treeAt memS 275 I3 P3 L3) = true := by quickRfl
theorem s4 : allN 88 (sortedAt 88 I4) = true := by quickRfl
theorem v4 : allN 88 (muVsAt memS 64 I4) = true := by quickRfl
theorem t4 : allN 88 (treeAt memS 88 I4 P4 L4) = true := by quickRfl
theorem sN : allN 4600 (sortedAt 4600 NB) = true := by quickRfl
theorem last : (memS (12288 ^^^ 64) == false) = true := by quickRfl

@[expose] noncomputable def nbF (k : Nat) : Bool := allFrom (230 * k) 230 (nbrAt memS NB)

#kc_each_unfold nbF 0 20 as CertificateChecks.KernelLeech.nb

@[expose] noncomputable def trF (k : Nat) : Bool :=
  allFrom (230 * k) 230 (treeAt memS 4600 NB NBP NBL)

#kc_each_unfold trF 0 20 as CertificateChecks.KernelLeech.tr

@[expose] noncomputable def m3F (k : Nat) : Bool :=
  allFrom (230 * k) 230 (muNbrAt memS 1 NB leechIdx3.toList)

#kc_each_unfold m3F 0 20 as CertificateChecks.KernelLeech.m3_

@[expose] noncomputable def m4F (k : Nat) : Bool :=
  allFrom (230 * k) 230 (muNbrAt memS 64 NB leechIdx4.toList)

#kc_each_unfold m4F 0 20 as CertificateChecks.KernelLeech.m4_

theorem nb_all : allN 4600 (nbrAt memS NB) = true := by
  refine of_blocks fun k hk => ?_
  interval_cases k
  exacts [nb0, nb1, nb2, nb3, nb4, nb5, nb6, nb7, nb8, nb9, nb10, nb11, nb12, nb13, nb14, nb15,
    nb16, nb17, nb18, nb19]

theorem tr_all : allN 4600 (treeAt memS 4600 NB NBP NBL) = true := by
  refine of_blocks fun k hk => ?_
  interval_cases k
  exacts [tr0, tr1, tr2, tr3, tr4, tr5, tr6, tr7, tr8, tr9, tr10, tr11, tr12, tr13, tr14, tr15,
    tr16, tr17, tr18, tr19]

theorem m3_all : allN 4600 (muNbrAt memS 1 NB leechIdx3.toList) = true := by
  refine of_blocks fun k hk => ?_
  interval_cases k
  exacts [m3_0, m3_1, m3_2, m3_3, m3_4, m3_5, m3_6, m3_7, m3_8, m3_9, m3_10, m3_11, m3_12, m3_13,
    m3_14, m3_15, m3_16, m3_17, m3_18, m3_19]

theorem m4_all : allN 4600 (muNbrAt memS 64 NB leechIdx4.toList) = true := by
  refine of_blocks fun k hk => ?_
  interval_cases k
  exacts [m4_0, m4_1, m4_2, m4_3, m4_4, m4_5, m4_6, m4_7, m4_8, m4_9, m4_10, m4_11, m4_12, m4_13,
    m4_14, m4_15, m4_16, m4_17, m4_18, m4_19]

theorem leech_ok : leechCheck = true := by
  have g3 : ∀ i < 275, leechIdx3[i]! = I3 i := fun i _ => arr_getK _ i
  have g4 : ∀ i < 88, leechIdx4[i]! = I4 i := fun i _ => arr_getK _ i
  have e1 := nbrOK_eq (klev := shortKlev) nbr_bind.1 nbr_bind.2
  have e2 := treeOK_eq (klev := shortKlev) nbr_bind.1 nbr_bind.2 nbrPar_bind.2 nbrLev_bind.2
  have e3 := muOK_eq (klev := shortKlev) (b := 1) nbr_bind.1 nbr_bind.2 sz3 g3
  have e4 := treeOK_eq (klev := shortKlev) sz3 g3 (PA := P3) (LV := L3)
    (fun i _ => arr_getK _ i) (fun i _ => arr_getK _ i)
  have e5 := muOK_eq (klev := shortKlev) (b := 64) nbr_bind.1 nbr_bind.2 sz4 g4
  have e6 := treeOK_eq (klev := shortKlev) sz4 g4 (PA := P4) (LV := L4)
    (fun i _ => arr_getK _ i) (fun i _ => arr_getK _ i)
  rw [shortHit_fun] at e1 e2 e3 e4 e5 e6
  have e7 : (shortHit shortKlev (12288 ^^^ 64) == false) = (memS (12288 ^^^ 64) == false) := by
    rw [shortHit_fun]
  have E : leechCheck = (andB (allN 4600 (sortedAt 4600 NB)) (allN 4600 (nbrAt memS NB)) &&
      allN 4600 (treeAt memS 4600 NB NBP NBL) &&
      andB (allN 275 (sortedAt 275 I3)) (andB (allN 275 (muVsAt memS 1 I3))
        (allN 4600 (muNbrAt memS 1 NB leechIdx3.toList))) &&
      allN 275 (treeAt memS 275 I3 P3 L3) &&
      andB (allN 88 (sortedAt 88 I4)) (andB (allN 88 (muVsAt memS 64 I4))
        (allN 4600 (muNbrAt memS 64 NB leechIdx4.toList))) &&
      allN 88 (treeAt memS 88 I4 P4 L4) &&
      (memS (12288 ^^^ 64) == false)) := by
    unfold leechCheck
    rw [e1, e2, e3, e4, e5, e6, e7]
  refine E.trans ?_
  simp only [andB_eq, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨sN, nb_all⟩, tr_all⟩, s3, v3, m3_all⟩, t3⟩, s4, v4, m4_all⟩, t4⟩, last⟩

end CertificateChecks.KernelLeech

end
