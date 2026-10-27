module

public import Certificates.Kernel.PropA.YFacts
public import Certificates.Kernel.PropA.PChk
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.A5Perfect

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PMem CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA
  CFSG.EvenSporadicStandard.M12Std.PropA.Native CFSG.EvenSporadicStandard.M12Std.Rbc

open scoped commutatorElement

section Conj

variable {G : Type*} [Group G] {D : Subgroup G} {k : G}

theorem pa450010_map_conj_D (hk : ∀ d ∈ D, k * d * k⁻¹ ∈ D) (hk' : ∀ d ∈ D, k⁻¹ * d * k⁻¹⁻¹ ∈ D) :
    D.map (MulAut.conj k).toMonoidHom = D := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hk z hz
  · intro hy
    refine ⟨k⁻¹ * y * k, ?_, ?_⟩
    · have h := hk' y hy
      rwa [inv_inv] at h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem pa450010_map_conj_inv_map (Q : Subgroup G) (k : G) :
    (Q.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom = Q := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom = MonoidHom.id G := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

theorem pa450010_map_conj_inv (hD : D.map (MulAut.conj k).toMonoidHom = D) :
    D.map (MulAut.conj k⁻¹).toMonoidHom = D := by
  have h := pa450010_map_conj_inv_map D k⁻¹
  rw [inv_inv] at h
  calc D.map (MulAut.conj k⁻¹).toMonoidHom
      = (D.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by rw [hD]
    _ = D := h

theorem pa450010_conj_inf_cent (hD : D.map (MulAut.conj k).toMonoidHom = D) (x : G) :
    (D ⊓ centralizer ({x} : Set G)).map (MulAut.conj k).toMonoidHom =
      D ⊓ centralizer ({k * x * k⁻¹} : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hD, map_conj_centralizer,
    Set.image_singleton, MulAut.conj_apply]

theorem pa450010_conj_inf_centS (hD : D.map (MulAut.conj k).toMonoidHom = D) (H : Subgroup G) :
    (D ⊓ centralizer (H : Set G)).map (MulAut.conj k).toMonoidHom =
      D ⊓ centralizer ((H.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hD, map_conj_centralizer,
    Subgroup.coe_map, MulEquiv.coe_toMonoidHom]

theorem pa450010_conj_jOf (hD : D.map (MulAut.conj k).toMonoidHom = D) (x : G) :
    (jOf D x).map (MulAut.conj k).toMonoidHom = jOf D (k * x * k⁻¹) := by
  unfold jOf
  rw [Subgroup.map_commutator, pa450010_conj_inf_cent hD]

theorem pa450010_isTwoA_conj {x : G} (h : IsTwoA D x) (hD : D.map (MulAut.conj k).toMonoidHom = D) :
    IsTwoA D (k * x * k⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hD]
    exact Subgroup.mem_map.2 ⟨x, h.mem, by simp [MulAut.conj_apply]⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_eq]
  · rw [← pa450010_conj_inf_cent hD x, Subgroup.card_map_of_injective (MulAut.conj k).injective,
      h.card_cent]
  · rw [← pa450010_conj_jOf hD x, ← pa450010_conj_inf_centS hD (jOf D x), h.cent_jOf,
      MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem pa450010_goodPerf_conj {r : G} (h : GoodPerf D (centralizer ({r} : Set G)))
    (hD : D.map (MulAut.conj k).toMonoidHom = D) :
    GoodPerf D (centralizer ({k * r * k⁻¹} : Set G)) := by
  intro Q hQ hQperf
  have hD' := pa450010_map_conj_inv hD
  have e : k⁻¹ * (k * r * k⁻¹) * k⁻¹⁻¹ = r := by group
  have hstep : (D ⊓ centralizer ({k * r * k⁻¹} : Set G)).map (MulAut.conj k⁻¹).toMonoidHom
      = D ⊓ centralizer ({r} : Set G) := by
    rw [pa450010_conj_inf_cent hD' (k * r * k⁻¹), e]
  have hmap : Q.map (MulAut.conj k⁻¹).toMonoidHom ≤ D ⊓ centralizer ({r} : Set G) :=
    hstep ▸ Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hQ
  have hperf : ⁅Q.map (MulAut.conj k⁻¹).toMonoidHom, Q.map (MulAut.conj k⁻¹).toMonoidHom⁆ =
      Q.map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [← Subgroup.map_commutator, hQperf]
  have hQ' := (pa450010_map_conj_inv_map Q k).symm
  rcases h _ hmap hperf with hbot | ⟨y, hy, hj⟩
  · left
    rw [hQ', hbot, Subgroup.map_bot]
  · right
    exact ⟨k * y * k⁻¹, pa450010_isTwoA_conj hy hD, by rw [hQ', hj, pa450010_conj_jOf hD y]⟩

theorem pa450010_sq_cases {t c : G} (ht : orderOf t = 2) (h : c ^ 2 ∈ zpowers t) :
    c * c = 1 ∨ c * c = t := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have hmod : t ^ (n % 2) = t ^ n := by
    have h1 := zpow_mod_orderOf t n
    rwa [ht, Nat.cast_ofNat] at h1
  have hc : c * c = t ^ n := by rw [hn, pow_two]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [hc, ← hmod, h0]
    exact zpow_zero t
  · right
    rw [hc, ← hmod, h1]
    exact zpow_one t

end Conj

theorem pa450010_cent_mul_pT (r : Perm (Fin 28)) :
    D28 ⊓ centralizer ({r * pT} : Set (Perm (Fin 28))) =
      D28 ⊓ centralizer ({r} : Set (Perm (Fin 28))) := by
  ext y
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun hy => ?_
  have hyt : y * pT = pT * y := by
    calc y * pT = pT * y * pT⁻¹ * pT := by rw [pT_comm_D28 y hy]
      _ = pT * y := by group
  constructor
  · intro h
    refine mul_right_cancel (b := pT) ?_
    calc y * r * pT = y * (r * pT) := by group
      _ = r * pT * y := h
      _ = r * (pT * y) := by group
      _ = r * (y * pT) := by rw [hyt]
      _ = r * y * pT := by group
  · intro h
    calc y * (r * pT) = y * r * pT := by group
      _ = r * y * pT := by rw [h]
      _ = r * (y * pT) := by group
      _ = r * (pT * y) := by rw [hyt]
      _ = r * pT * y := by group

theorem pa450010_good_mul_pT {r : Perm (Fin 28)} (h : GoodPerf D28 (centralizer ({r} : Set _))) :
    GoodPerf D28 (centralizer ({r * pT} : Set (Perm (Fin 28)))) := by
  intro Q hQ
  rw [pa450010_cent_mul_pT] at hQ
  exact h Q hQ

theorem pa450010_J_sq : ∀ Q' : Subgroup (Perm (Fin 28)),
    (∀ g ∈ jOf D28 pa450010x, g * g ∈ Q') → jOf D28 pa450010x ≤ Q' := by
  intro Q' hQ'
  rw [pa450010_jOf_eq] at hQ' ⊢
  rw [← pa450010_J_perf, commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Q'.mul_mem (Q'.mul_mem (hQ' a ha) (hQ' _ (mul_mem (inv_mem ha) hb))) (hQ' _ (inv_mem hb))

theorem pa450010_perf2A : Perf2A D28 pa450010x := by
  refine ⟨⟨pa450010_x_memD, pa450010_x_order, pa450010_card_Dx, ?_⟩, ?_⟩
  · rw [pa450010_jOf_eq]
    exact pa450010_CDJ
  · intro Q hQ hperf
    have hQJ : Q ≤ jOf D28 pa450010x := by
      calc Q = ⁅Q, Q⁆ := hperf.symm
        _ ≤ jOf D28 pa450010x := Subgroup.commutator_mono hQ hQ
    exact eq_bot_or_eq_of_perfect_of_card_sixty pa450010_card_J pa450010_J_sq Q hQJ hperf

theorem pa450010_good_of_perf2A {x : Perm (Fin 28)} (hP : Perf2A D28 x) :
    GoodPerf D28 (centralizer ({x} : Set (Perm (Fin 28)))) := by
  intro Q hQ hperf
  rcases hP.perfect Q hQ hperf with hbot | hj
  · exact Or.inl hbot
  · exact Or.inr ⟨x, hP.toIsTwoA, hj⟩

theorem pa450010_wv_A (b : Bool) : pa450010wv b 2 [1] = pA :=
  pa450010wv_wD b 0 (by norm_num)

theorem pa450010_card_DA :
    Nat.card ↥(D28 ⊓ centralizer ({pA} : Set (Perm (Fin 28)))) = 192 := by
  have hr : PRep 28 5 pa450010AD.R pA := by
    have h := pa450010_root (b := false) (kS := 2) (by norm_num) pa450010_AD_root
    rwa [pa450010_wv_A] at h
  have hA : pA ∈ D28 := by
    rw [← pa450010_wv_A false]
    exact pa450010wv_memD false _
  obtain ⟨c, -, hinj, hN, hcls⟩ := pa450010_conj (b := false) (by norm_num) hr pa450010_AD_hd
    pa450010_AD_sl
  rw [pa450010_clD] at hcls
  have h := pa450010_size hA hcls hinj
  rw [hN, card_D28] at h
  omega

theorem pa450010_good_A :
    GoodPerf D28 (centralizer ({pA} : Set (Perm (Fin 28)))) := by
  intro Q hQ hperf
  left
  by_contra hne
  have hsol : Group.IsSolvable ↥(D28 ⊓ centralizer ({pA} : Set (Perm (Fin 28)))) := by
    have : Fintype ↥(D28 ⊓ centralizer ({pA} : Set (Perm (Fin 28)))) := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 6) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, pa450010_card_DA]
    norm_num
  have hQsol : Group.IsSolvable ↥Q := solvable_of_solvable_injective (Subgroup.inclusion_injective hQ)
  have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥Q hQsol

theorem pa450010_cl_le_centZ {b : Bool} {kS k Z : ℕ} {G : ℕ → ℕ} {ws : List (List Int)}
    {z : Perm (Fin 28)} (hk : k = ws.length) (hg : ∀ j < k, PRep 28 5 (G j) (pa450010wv b kS ws[j]!))
    (hz : PRep 28 5 Z z) (hc : centK 28 5 (mask 5) (28 * 5) k G Z = true) :
    pa450010cl b kS ws ≤ centralizer ({z} : Set (Perm (Fin 28))) := by
  have h := closure_le_centralizer (by norm_num) hg hz hc
  subst hk
  exact h

@[expose] noncomputable def pa450010d : Perm (Fin 28) := pa450010wv false 2 pa450010wd

theorem pa450010_prepZd : PRep 28 5 (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010PD 0)
    pa450010XD.R) (pa450010PD 1)) (pa450010d * pa450010x * pa450010d⁻¹) := by
  have h := pa450010_PD_ok
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hd : PRep 28 5 (pa450010PD 0) pa450010d := pa450010_root (b := false) (by norm_num) h.1
  exact prep_pcomp (by norm_num) (prep_pcomp (by norm_num) hd pa450010_prepX)
    (CFSG.KC.OrbGroup.prep_inv hd h.2)

theorem pa450010_CKG (b : Bool) :
    K28 b ⊓ centralizer ({pG b} : Set (Perm (Fin 28))) ≤
      centralizer ({pa450010d * pa450010x * pa450010d⁻¹} : Set (Perm (Fin 28))) := by
  have hsz := pa450010_sizeK b 4 (by norm_num)
  rw [(pa450010_rep_eq b).2.2.1] at hsz
  have hcK : Nat.card ↥(K28 b ⊓ centralizer ({pG b} : Set (Perm (Fin 28)))) = 480 := by
    change 792 * _ = 380160 at hsz
    omega
  have key : ∀ {k : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ} {cnt : ℕ},
      recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 480 k G GI cnt T PL 4
        (pa450010S b) (pa450010SI b) pa450010wCKG = true →
      penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 480 = true →
      centK 28 5 (mask 5) (28 * 5) k G (pa450010S b 2) = true →
      centK 28 5 (mask 5) (28 * 5) k G (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010PD 0)
        pa450010XD.R) (pa450010PD 1)) = true →
      K28 b ⊓ centralizer ({pG b} : Set (Perm (Fin 28))) ≤
        centralizer ({pa450010d * pa450010x * pa450010d⁻¹} : Set (Perm (Fin 28))) := by
    intro k G GI T PL POS SRT SRI cnt hd hsl hcg hcz
    obtain ⟨-, -, -, -, hcard, hk, hg, -⟩ := pa450010_rec (by norm_num) hd hsl
    have hle : pa450010cl b 4 pa450010wCKG ≤ K28 b ⊓ centralizer ({pG b} : Set (Perm (Fin 28))) :=
      le_inf (pa450010_cl_le_K b 4 _)
        (pa450010_cl_le_centZ hk hg (pa450010_prepS b 2 (by norm_num)) hcg)
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcK])
    rw [← heq]
    exact pa450010_cl_le_centZ hk hg pa450010_prepZd hcz
  cases b
  · have hc := pa450010_CKG1_cent
    rw [bAnd_eq, Bool.and_eq_true] at hc
    exact key pa450010_CKG1_hd pa450010_CKG1_sl hc.1 hc.2
  · have hc := pa450010_CKG2_cent
    rw [bAnd_eq, Bool.and_eq_true] at hc
    exact key pa450010_CKG2_hd pa450010_CKG2_sl hc.1 hc.2

theorem pa450010_good_G (b : Bool) :
    GoodPerf D28 (centralizer ({pG b} : Set (Perm (Fin 28)))) := by
  have hdD : pa450010d ∈ D28 := pa450010wv_memD false _
  have hP := pa450010_perf2A.conj hdD
  intro Q hQ hperf
  have hQz : Q ≤ D28 ⊓ centralizer ({pa450010d * pa450010x * pa450010d⁻¹} : Set _) :=
    le_inf (hQ.trans inf_le_left) fun y hy =>
      pa450010_CKG b ⟨D28_le_K28 b (hQ hy).1, (hQ hy).2⟩
  rcases hP.perfect Q hQz hperf with hbot | hj
  · exact Or.inl hbot
  · exact Or.inr ⟨_, hP.toIsTwoA, hj⟩

theorem pa450010_rep01 (b : Bool) : pa450010rep b 0 = pA ∧ pa450010rep b 1 = pA * pT := by
  have hl : ∀ wd : List Int, (∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ 4) →
      pa450010wv b 4 wd = wordP (pa450010gK b) 4 wd := pa450010wv_eq_wordP b 4
  have h1 : wordP (pa450010gK b) 4 [1] = pA := by
    simp [wordP, CFSG.Sporadic.Th.wordG, letterG, pa450010gK]
  refine ⟨?_, ?_⟩
  · change pa450010wv b 4 [1] = _
    rw [hl _ (by simp), h1]
  · change pa450010wv b 4 ([1] ++ [4]) = _
    rw [hl _ (by simp), pa450010_wordP_append, h1, pa450010_wordP_4]

theorem pa450010_good (b : Bool) :
    ∀ i < 6, GoodPerf D28 (centralizer ({pa450010rep b i} : Set (Perm (Fin 28)))) := by
  intro i hi
  obtain ⟨e0, e1⟩ := pa450010_rep01 b
  obtain ⟨e2, e3, e4, e5⟩ := pa450010_rep_eq b
  interval_cases i
  · rw [e0]
    exact pa450010_good_A
  · rw [e1]
    exact pa450010_good_mul_pT pa450010_good_A
  · rw [e2]
    exact pa450010_good_of_perf2A pa450010_perf2A
  · rw [e3]
    exact pa450010_good_mul_pT (pa450010_good_of_perf2A pa450010_perf2A)
  · rw [e4]
    exact pa450010_good_G b
  · rw [e5]
    exact pa450010_good_mul_pT (pa450010_good_G b)

theorem pa450010_perfect_cent (b : Bool) :
    ∀ c ∈ K28 b, c ^ 2 ∈ zpowers pT → c ∉ zpowers pT →
      ∀ Q ≤ D28 ⊓ centralizer ({c} : Set (Perm (Fin 28))), ⁅Q, Q⁆ = Q → Q = ⊥ ∨
        ∃ x ∈ D28, orderOf x = 2 ∧ Nat.card ↥(D28 ⊓ centralizer ({x} : Set (Perm (Fin 28)))) = 240 ∧
          Q = jOf D28 x ∧ D28 ⊓ centralizer (jOf D28 x : Set (Perm (Fin 28))) = zpowers x := by
  intro c hc hc2 hcn Q hQ hperf
  have ht2 : orderOf pT = 2 := orderOf_eq_prime (by rw [pow_two]; exact pT_mul_self)
    pa450010_pT_ne_one
  have hsq := pa450010_sq_cases ht2 hc2
  have h1 : c ≠ 1 := fun h => hcn (h ▸ one_mem _)
  have ht : c ≠ pT := fun h => hcn (h ▸ mem_zpowers pT)
  obtain ⟨i, hi, ⟨k, hk, rfl⟩, -⟩ := pa450010_cover b hc hsq h1 ht
  have hD : D28.map (MulAut.conj k).toMonoidHom = D28 :=
    pa450010_map_conj_D (D28_conj b k hk) (D28_conj b k⁻¹ (inv_mem hk))
  rcases pa450010_goodPerf_conj (pa450010_good b i hi) hD Q hQ hperf with hbot | ⟨x', hx', hQx'⟩
  · exact Or.inl hbot
  · exact Or.inr ⟨x', hx'.mem, hx'.orderOf_eq, hx'.card_cent, hQx', hx'.cent_jOf⟩

end CertificateChecks.KernelPropA

end
