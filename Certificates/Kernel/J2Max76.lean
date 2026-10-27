module

public import Certificates.Data.Kernel.J2Max76
import Certificates.Kernel.J2Max76.Fast
import CFSG.Certificates.Kernel.J2Max76FastSound
import CFSG.Certificates.Kernel.J2Max76PackSound
import CFSG.Certificates.Kernel.MonsterB.NatBfsLSound

public section

namespace CertificateChecks.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs
  CFSG.KC.J2Max76 CertificateChecks.KernelJ2Max76

theorem orbitSearch_eq_L (act : ℕ → ℕ → ℕ) (nh N : ℕ) :
    orbitSearch act nh N = orbitSearchL act nh N := by
  unfold orbitSearch orbitSearchL
  rw [natBfs_eq_natBfsL_fun]

theorem repOK_eq_L (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) :
    repOK c hp r = repOKL c hp r := by
  unfold repOK repOKL
  rw [natBfs_eq_natBfsL_fun]

private theorem tabs_size : nTabsL.size = 3 := by
  have h := tabs_pin
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem tabs_pinT : pinT nTabsP 9 280 (nTabsL.toList.map Array.toList) = true := by
  have h := tabs_pin
  rw [Bool.and_eq_true] at h
  exact h.2

private theorem tab_eq : tabOf orbLit = tabR orbEdgesP :=
  tabOf_eq_R orbLit orbEdgesP (certPin_edges _ _ _ _ _ _ _ _ orb_pin)

private theorem orbLit_size : orbLit.pts.size = 280 := certPin_size _ _ _ _ _ _ _ _ orb_pin

private theorem rp_eq (w : List ℕ) (rp : Array ℕ) (h : (permL (tabR orbEdgesP) 280 w == rp.toList) = true) :
    permArr orbLit w = rp := by
  apply Array.toList_inj.mp
  rw [permArr_toList, tab_eq, orbLit_size]
  exact beq_iff_eq.mp h

private theorem rep1 : repOKL orbLit nTabsL 1 = true :=
  repOKL_of _ _ _ _ _ _ (beq_iff_eq.mp w1_lit) (rp_eq _ _ rp1_lit)
    (by rw [repAct_eq_R _ _ _ _ tabs_size tabs_pinT rp1_pin]; exact certEqB_eq _ _ c1_lit)
    (repLitOK_of_P _ _ _ _ _ _ _ _ _ _ _ _ tabs_size tabs_pinT rp1_pin c1_pin rep1_ok)

private theorem rep15 : repOKL orbLit nTabsL 15 = true :=
  repOKL_of _ _ _ _ _ _ (beq_iff_eq.mp w15_lit) (rp_eq _ _ rp15_lit)
    (by rw [repAct_eq_R _ _ _ _ tabs_size tabs_pinT rp15_pin]; exact certEqB_eq _ _ c15_lit)
    (repLitOK_of_P _ _ _ _ _ _ _ _ _ _ _ _ tabs_size tabs_pinT rp15_pin c15_pin rep15_ok)

private theorem rep18 : repOKL orbLit nTabsL 18 = true :=
  repOKL_of _ _ _ _ _ _ (beq_iff_eq.mp w18_lit) (rp_eq _ _ rp18_lit)
    (by rw [repAct_eq_R _ _ _ _ tabs_size tabs_pinT rp18_pin]; exact certEqB_eq _ _ c18_lit)
    (repLitOK_of_P _ _ _ _ _ _ _ _ _ _ _ _ tabs_size tabs_pinT rp18_pin c18_pin rep18_ok)

private theorem reps_ok : (orbsLit.all fun t => t.1 == 0 || repOKL orbLit nTabsL t.1) = true := by
  rw [orbsLit.eq_1]
  simp only [List.all_cons, List.all_nil, rep1, rep15, rep18, Bool.or_true, Bool.and_true,
    beq_self_eq_true, Bool.true_or]

private theorem orbs_ok : okOrbs nTabsL 280 orbsLit = true := by
  refine okOrbs_of _ _ _ (fun t ht => ?_) orbs_cover
  rw [hAct_eq_R _ _ tabs_pinT, tabs_size]
  rw [orbsLit.eq_1] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o0_pin).trans o0_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o1_pin).trans o1_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o15_pin).trans o15_ok
  · exact (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ o18_pin).trans o18_ok

theorem check_true : check () = true := by
  have hroot : root () = rootLit := beq_iff_eq.mp root_lit
  have hact : act = actK gensL := act_eq_actK gensL gens_lit
  have e0 : orbitCert () = natBfsL act 5 (root ()) 280 := natBfs_eq_natBfsL _ _ _ _
  rw [hact, hroot, certEqB_eq _ _ orb_lit] at e0
  have ht : nTabs orbLit = nTabsL := arrEq _ _ (by
    rw [nTabs_toList, tab_eq, orbLit_size]
    exact tabs_lit)
  have ho : orbitSearch (hAct nTabsL) 3 280 = orbsLit := by
    rw [orbitSearch_eq_L, hAct_eq_R _ _ tabs_pinT]
    exact orbsEqB_eq _ _ orbs_lit
  have hok : natCertOK (actK gensL) 5 (fun u => decide (u < 2 ^ 315)) rootLit orbLit = true :=
    (natCertOK_eq_P _ _ _ _ _ _ _ _ _ _ _ orb_pin).trans orb_ok
  have hc : check () = (natCertOK (actK gensL) 5 (fun u => decide (u < 2 ^ 315)) rootLit orbLit &&
      orbLit.pts.size == 280 && (List.range 3).all (fun s => tabOf orbLit (s + 2) 0 == 0) &&
      okOrbs nTabsL 280 orbsLit &&
      orbsLit.all fun t => t.1 == 0 || repOKL orbLit nTabsL t.1) := by
    unfold check
    simp only [e0, ht, ho, repOK_eq_L, hact, hroot]
  rw [hc, hok, orb_size, orb_fix, orbs_ok, reps_ok]
  rfl

end CertificateChecks.J2Max76
