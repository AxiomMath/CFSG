module

public import Certificates.Kernel.Fi23Cov.Words
public import Certificates.Kernel.Fi23Cov.FiveH
public import Certificates.Kernel.Fi23Cov.FiveA0
public import Certificates.Kernel.Fi23Cov.FiveA1
public import Certificates.Kernel.Fi23Cov.FiveB
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTwoCent
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.Fi23Cov

#kc_forall_tree let_all (fun j => CFSG.KD.Fi23Cov.letc j = true) 14 CFSG.KD.Fi23Cov.Ck.l
#kc_forall_tree stA_all (fun k => CFSG.KD.Fi23Cov.stA k = true) 51 CFSG.KD.Fi23Cov.Ck.a
#kc_forall_tree stB_all (fun k => CFSG.KD.Fi23Cov.stB k = true) 36 CFSG.KD.Fi23Cov.Ck.b

open CFSG.KC.Fi23Cov CFSG.Sporadic.Fi23 CFSG.StandardType.SporadicShape


theorem val_five : (Nat.card ↥CFSG.Sporadic.Fi23.J).factorization 5 = 2 := by
  rw [CFSG.Sporadic.Fi23.card_J, Nat.factorization_def 4089470473293004800 (p := 5) (by norm_num)]
  have hc : padicValNat 5 163578818931720192 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 163578818931720192)
  have e1 : (4089470473293004800 : ℕ) = 5 * (5 * 163578818931720192) := by norm_num
  rw [e1, padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), hc]


theorem sporKRestCover_five_J : SporKRestCover 5 ↥CFSG.Sporadic.Fi23.J := by
  have hH := Ck.head
  unfold head fHead at hH
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM, hRa⟩, hRb⟩, h1w⟩, h2w⟩, hhw⟩, hMc⟩, hRac⟩, hRbc⟩, hp1⟩, hp2⟩, hne⟩,
    hc⟩, hcj⟩ := hH
  have hMl := (lenLe_iff _ _).1 hM
  have hRal := (lenLe_iff _ _).1 hRa
  have hRbl := (lenLe_iff _ _).1 hRb
  have o1 := okW_of_chW h1w
  have o2 := okW_of_chW h2w
  have oh := okW_of_chW hhw
  have oM := okW_nthW hMc
  have h1 : wJ F.U1 ^ 5 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW o1 5) okW_nil hp1
  have h2 : wJ F.U2 ^ 5 = 1 := by
    rw [← wJ_repW, ← wJ_nil]
    exact eqw (okW_repW o2 5) okW_nil hp2
  have hne1 : wJ F.U1 ≠ 1 := by
    intro h
    rw [← wJ_nil] at h
    rw [E_of_eq o1 okW_nil h] at hne
    exact Bool.noConfusion hne
  have hc' := comm_of o1 o2 hc
  have hh : wJ F.U1 * wJ F.H = wJ F.H * wJ F.U2 := by
    have e := eqw (okW_append oh o1) (okW_append o2 oh) hcj
    rwa [wJ_append, wJ_append] at e
  let L : Subgroup J := Subgroup.closure
    ((Subgroup.centralizer {wJ F.U1} : Set J) ∪ Subgroup.centralizer {wJ F.U2})
  have hlet : ∀ k, wJ (nthW F.M k) ∈ L := by
    refine wJ_mem_of_nthW hMl fun k hk => ?_
    have hj14 : k / 2 < 14 := by omega
    have hj := let_all (k / 2) hj14
    unfold letc fLet at hj
    rw [Bool.and_eq_true, Bool.or_eq_true] at hj
    obtain ⟨hinv, hj⟩ := hj
    have hw : wJ (nthW F.M (2 * (k / 2))) ∈ L := by
      apply Subgroup.subset_closure
      rcases hj with hj | hj
      · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 (comm_of (oM _) o1 hj))
      · exact Or.inr (Subgroup.mem_centralizer_singleton_iff.2 (comm_of (oM _) o2 hj))
    have hinv' := eqw (okW_append (oM _) (oM _)) okW_nil hinv
    rw [wJ_append, wJ_nil, mul_eq_one_iff_eq_inv] at hinv'
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have e : 2 * j / 2 = j := by omega
      rwa [e] at hw
    · have e : (2 * j + 1) / 2 = j := by omega
      rw [e] at hw hinv'
      rw [hinv']
      exact L.inv_mem hw
  have hstA : ∀ k, wJ (nthW F.Ra k) ∈ L := by
    refine wJ_mem_of_nthW hRal fun k hk => ?_
    have hs := stA_all k hk
    unfold stA stOK at hs
    rw [← eqw (okW_expC hMc _) (okW_nthW hRac k) hs]
    exact wJ_mem_expC hlet _
  have hstB : ∀ k, wJ (nthW F.Rb k) ∈ L := by
    refine wJ_mem_of_nthW hRbl fun k hk => ?_
    have hs := stB_all k hk
    unfold stB stOK at hs
    rw [← eqw (okW_expC hMc _) (okW_nthW hRbc k) hs]
    exact wJ_mem_expC hlet _
  have ha : a ∈ L := by
    have hp := Ck.pa
    unfold prA prOK at hp
    rw [← wJ_39, ← eqw (okW_catW hRac) (okW_lit (by decide)) hp]
    exact wJ_mem_catW' hstA
  have hb : b ∈ L := by
    have hp := Ck.pb
    unfold prB prOK at hp
    rw [← wJ_40, ← eqw (okW_catW hRbc) (okW_lit (by decide)) hp]
    exact wJ_mem_catW' hstB
  have hgen : L = ⊤ := by
    rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ha
    · exact hb
  exact sporKRest_cover_of_twoCent Nat.prime_five val_five hne1 h1 h2 hc' hh hgen

end CFSG.KD.Fi23Cov

end
