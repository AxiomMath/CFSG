module

public import Certificates.Kernel.G24Th799103.GlueM
public import CFSG.RankThree.Asc83Table.E9
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open CFSG.Sporadic.Co1Block (twoBD xBar yBar)
open CertificateChecks.KernelG24.Tri27206

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem closure_mul_mem {s : Set Pm} {S : Finset Pm} (hS : ∀ g ∈ s, ∀ t ∈ S, g * t ∈ S) {x : Pm}
    (hx : x ∈ Subgroup.closure s) : ∀ t ∈ S, x * t ∈ S := by
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one =>
    intro t ht
    rwa [one_mul]
  | mul x y _ _ hx hy =>
    intro t ht
    rw [mul_assoc]
    exact hx _ (hy t ht)
  | inv x _ hx =>
    intro t ht
    obtain ⟨u, hu, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := S)
      (fun a _ => x * a) (fun a ha => hx a ha) (fun a b _ _ h => mul_left_cancel h) le_rfl t ht
    rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hu

theorem toPerm_powG {g : Nat} (hg : PP 1365 11 g) :
    ∀ e, PP 1365 11 (powG g e) ∧ toPerm 1365 11 (powG g e) = toPerm 1365 11 g ^ e
  | 0 => ⟨PP.id g24sz, toPerm_one⟩
  | e + 1 => by
    obtain ⟨hp, he⟩ := toPerm_powG hg e
    refine ⟨hg.mul hp, ?_⟩
    change toPerm 1365 11 (mulG g (powG g e)) = _
    rw [toPerm_mulG hg hp, he, pow_succ']

theorem pp_pG : ∀ k < 2, PP 1365 11 (pG k) := fun k hk =>
  pp_of (band (Orb.allN_iff.1 (band ch799103_bpd).1 k hk)).1

theorem pp_dK : ∀ k < 4, PP 1365 11 (dK k) := fun k hk =>
  pp_of (band (Orb.allN_iff.1 (band ch799103_bpd).2 k hk)).1

theorem PL_len : PL.length = 27 := Nat.eq_of_beq_eq_true (band ch799103_bpl).2

theorem pL_facts : ∀ i < 27, PP 1365 11 (pL i) ∧
    toPerm 1365 11 (pL i) ∈ Subgroup.closure (gens 1365 11 pG 2) := fun i hi => by
  have hr : PL.getD i (0, 0, 0, 0) ∈ PL := by
    rw [List.getD_eq_getElem _ _ (by rw [PL_len]; exact hi)]
    exact List.getElem_mem _
  exact (mulRecK_sound g24sz pp_pG (band ch799103_bpl).1).1 _ hr

noncomputable abbrev gP3 : Subgroup Pm := Subgroup.closure (gens 1365 11 pG 2)

theorem mem_P3_iff {x : Pm} (hx : x ∈ gP3) : ∃ i < 27, toPerm 1365 11 (pL i) = x := by
  classical
  set S : Finset Pm := (Finset.range 27).image fun i => toPerm 1365 11 (pL i)
  have hS : ∀ g ∈ gens 1365 11 pG 2, ∀ t ∈ S, g * t ∈ S := by
    rintro _ ⟨k, hk, rfl⟩ t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    have hi' : i < 27 := Finset.mem_range.1 hi
    obtain ⟨hlt, he⟩ := band (Orb.allN_iff.1 (Orb.allN_iff.1 ch799103_bcl i hi') k hk)
    have hc := lt_of_blt hlt
    refine Finset.mem_image.2 ⟨_, Finset.mem_range.2 hc, ?_⟩
    rw [← eq_of_beq he, toPerm_mulG (pp_pG k hk) (pL_facts i hi').1]
  have h0 := pL_facts 0 (by norm_num)
  have hm := closure_mul_mem hS (gP3.mul_mem hx (gP3.inv_mem h0.2)) (toPerm 1365 11 (pL 0))
    (Finset.mem_image.2 ⟨0, by simp, rfl⟩)
  rw [inv_mul_cancel_right] at hm
  obtain ⟨i, hi, e⟩ := Finset.mem_image.1 hm
  exact ⟨i, Finset.mem_range.1 hi, e⟩

theorem card_P3 : Nat.card gP3 = 27 := by
  classical
  refine le_antisymm ?_ (PL_len ▸ le_card_of_mulRecK g24sz pp_pG (band ch799103_bpl).1)
  have hsub : (gP3 : Set Pm) ⊆ ↑((Finset.range 27).image fun i => toPerm 1365 11 (pL i)) :=
    fun x hx => by
      obtain ⟨i, hi, rfl⟩ := mem_P3_iff hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)
  calc Nat.card gP3 = (gP3 : Set Pm).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑((Finset.range 27).image fun i => toPerm 1365 11 (pL i)) : Set Pm).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 27 := by
      rw [Set.ncard_coe_finset]
      exact (Finset.card_image_le).trans (by simp)

theorem cube_pL {i : Nat} (hi : i < 27) :
    toPerm 1365 11 (pL i) ^ 2 = toPerm 1365 11 (pL (SQ.getD i 0)) ∧
      toPerm 1365 11 (pL i) ^ 3 = 1 := by
  obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 ch799103_bsq i hi)
  obtain ⟨h1, h2⟩ := band h12
  have p := (pL_facts i hi).1
  have q := (pL_facts _ (lt_of_blt h1)).1
  have e2 := eq_of_beq h2
  rw [toPerm_mulG p p] at e2
  have e3 := eq_of_beq h3
  rw [toPerm_mulG p q, toPerm_one] at e3
  refine ⟨by rw [sq, e2], ?_⟩
  rw [pow_succ', sq, e2, e3]


theorem P3_le : gP3 ≤ twoBD := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_D_of_inDK (pp_pG k hk) (band (Orb.allN_iff.1 (band ch799103_bpd).1 k hk)).2

theorem exists_conj_le_P3 {E : Subgroup Pm} (hED : E ≤ twoBD) (hE9 : Nat.card E = 9) :
    ∃ g ∈ twoBD, E.map (MulAut.conj g).toMonoidHom ≤ gP3 := by
  have hc : Nat.card (E.subgroupOf twoBD) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv, hE9]
  have hEp : IsPGroup 3 (E.subgroupOf twoBD) := IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
  obtain ⟨S, hS⟩ := hEp.exists_le_sylow
  have hPc : Nat.card (gP3.subgroupOf twoBD) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le).toEquiv, card_P3]
  have hPp : IsPGroup 3 (gP3.subgroupOf twoBD) :=
    IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  have hPi : ¬ 3 ∣ (gP3.subgroupOf twoBD).index := by
    intro h3
    have h := Subgroup.index_mul_card (H := gP3.subgroupOf twoBD)
    rw [hPc, CFSG.Sporadic.Co1Block.card_twoBD] at h
    have h' : (gP3.subgroupOf twoBD).index = 9318400 := by omega
    rw [h'] at h3
    norm_num at h3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq twoBD S (hPp.toSylow hPi)
  have h := congrArg (fun S : Sylow 3 twoBD => (S : Subgroup twoBD)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.pointwise_smul_def] at h
  have h' : (S : Subgroup twoBD).map (MulAut.conj g).toMonoidHom = gP3.subgroupOf twoBD := h
  refine ⟨g, g.2, ?_⟩
  have h1 : (E.subgroupOf twoBD).map (MulAut.conj g).toMonoidHom ≤ gP3.subgroupOf twoBD :=
    h' ▸ Subgroup.map_mono hS
  have h2 := Subgroup.map_mono (f := twoBD.subtype) h1
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left P3_le] at h2
  have hcomp : twoBD.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Pm)).toMonoidHom.comp twoBD.subtype :=
    MonoidHom.ext fun _ => rfl
  rwa [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hED] at h2

noncomputable abbrev gE0 : Subgroup Pm :=
  Subgroup.closure {permOfArr 1365 g24ThC1, permOfArr 1365 g24ThC2}

theorem card_E0 : Nat.card gE0 = 9 := by
  obtain ⟨h3, h3', hc, h1, h2, h21, h22, -⟩ := basic_facts
  exact CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine h3 h3' hc h1
    (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne h3 h2 h21 h22)

theorem e9_mem {c : Nat} (hc : c < 9) : toPerm 1365 11 (e9 c) ∈ gE0 := by
  have p0 := pp_TG3 0 (by norm_num)
  have p1 := pp_TG3 1 (by norm_num)
  have e := Orb.allN_iff.1 (Orb.allN_iff.1 ch799103_be9 (c / 3) (by omega)) (c % 3) (by omega)
  have hidx : Nat.add (Nat.mul 3 (c / 3)) (c % 3) = c := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [hidx] at e
  obtain ⟨pa, ea⟩ := toPerm_powG p0 (c / 3)
  obtain ⟨pb, eb⟩ := toPerm_powG p1 (c % 3)
  rw [eq_of_beq e, toPerm_mulG pa pb, ea, eb, toPerm_TG (by norm_num) p0,
    toPerm_TG (by norm_num) p1]
  exact gE0.mul_mem (gE0.pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
    (gE0.pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) _)

theorem exists_conj_eq_E0_of_le {F : Subgroup Pm} (hFP : F ≤ gP3) (hF9 : Nat.card F = 9) :
    ∃ d ∈ twoBD, F.map (MulAut.conj d).toMonoidHom = gE0 := by
  have h3 : ∀ z ∈ F, z ^ 3 = 1 := fun z hz => by
    obtain ⟨i, hi, rfl⟩ := mem_P3_iff (hFP hz)
    exact (cube_pL hi).2
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF9
    norm_num at hF9
  obtain ⟨⟨x, hxF⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 := h3 x hxF
  obtain ⟨y, hyF, hyx⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun z hz => hcon z hz : F ≤ Subgroup.zpowers x)
    rw [hF9, Nat.card_zpowers] at hle
    have := orderOf_le_of_pow_eq_one (by norm_num) hx3
    omega
  have hy3 := h3 y hyF
  have hxy : x * y = y * x := congrArg Subtype.val
    (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := F) (by rw [hF9]; norm_num)
      ⟨x, hxF⟩ ⟨y, hyF⟩)
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hyx1 : y ≠ x := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hyx2 : y ≠ x ^ 2 := fun h => hyx (h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
  obtain ⟨i, hi, rfl⟩ := mem_P3_iff (hFP hxF)
  obtain ⟨j, hj, rfl⟩ := mem_P3_iff (hFP hyF)
  have pi := (pL_facts i hi).1
  have pj := (pL_facts j hj).1
  obtain ⟨hcj12, hcj⟩ := band ch799103_bcj
  obtain ⟨hpo, -⟩ := band hcj12
  have hPO : PO < 1365 := lt_of_blt hpo
  have h' := Orb.allN_iff.1 (Orb.allN_iff.1 ch799103_bpairs i hi) j hj
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h'
  rcases h' with ((((h' | h') | h') | h') | h') | h'
  · have e := congrArg (fun g : Pm => (g ⟨PO, hPO⟩ : Nat)) hxy
    simp only [Equiv.Perm.mul_apply, toPerm_apply pi, toPerm_apply pj] at e
    rw [e, Nat.beq_refl] at h'
    exact absurd h' (by decide)
  · exact absurd (by rw [eq_of_beq h', toPerm_one]) hx1'
  · exact absurd (by rw [eq_of_beq h', toPerm_one]) hy1
  · exact absurd (by rw [Nat.eq_of_beq_eq_true h']) hyx1
  · exact absurd (by rw [Nat.eq_of_beq_eq_true h', (cube_pL hi).1]) hyx2
  unfold cjPair at h'
  rw [List.any_eq_true] at h'
  obtain ⟨k, hk, hk'⟩ := h'
  rw [List.mem_range] at hk
  obtain ⟨hki, hkj⟩ := band hk'
  have hconj : ∀ m (hm : m < 27), Nat.blt (CJ.getD (Nat.add (Nat.mul 27 k) m) 9) 9 = true →
      toPerm 1365 11 (dK k) * toPerm 1365 11 (pL m) * (toPerm 1365 11 (dK k))⁻¹ ∈ gE0 := by
    intro m hm hlt
    have hlt' : Nat.add (Nat.mul 27 k) m < 108 := by
      change 27 * k + m < 108
      omega
    have e := Orb.allN_iff.1 hcj _ hlt'
    have hdiv : Nat.div (Nat.add (Nat.mul 27 k) m) 27 = k := by
      change (27 * k + m) / 27 = k
      omega
    have hmod : Nat.mod (Nat.add (Nat.mul 27 k) m) 27 = m := by
      change (27 * k + m) % 27 = m
      omega
    rw [hdiv, hmod, hlt, Bool.true_and] at e
    simp only [Bool.or_eq_true] at e
    rcases e with e | e
    · rw [Nat.ble_eq] at e
      rw [Nat.blt_eq] at hlt
      omega
    · rw [← toPerm_conjP (pp_dK k hk) (pL_facts m hm).1, eq_of_beq e]
      exact e9_mem (lt_of_blt hlt)
  have hdx := hconj i hi hki
  have hdy := hconj j hj hkj
  have hdD : toPerm 1365 11 (dK k) ∈ twoBD :=
    mem_D_of_inDK (pp_dK k hk) (band (Orb.allN_iff.1 (band ch799103_bpd).2 k hk)).2
  refine ⟨_, hdD, ?_⟩
  set x := toPerm 1365 11 (pL i)
  set y := toPerm 1365 11 (pL j)
  have hcl : Subgroup.closure {x, y} ≤ F := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hxF, hyF⟩
  have hFeq : Subgroup.closure {x, y} = F := Subgroup.eq_of_le_of_card_ge hcl (by
    rw [CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3 hy3 hxy hx1'
      (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hx3 hy1 hyx1 hyx2), hF9])
  have hle : F.map (MulAut.conj (toPerm 1365 11 (dK k))).toMonoidHom ≤ gE0 := by
    rw [← hFeq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · simpa [MulAut.conj_apply] using hdx
    · simpa [MulAut.conj_apply] using hdy
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_E0, Subgroup.card_map_of_injective (MulAut.conj _).injective, hF9])

theorem conj_E0 {E : Subgroup Pm} (hED : E ≤ twoBD) (hE9 : Nat.card E = 9) :
    ∃ g ∈ twoBD, gE0.map (MulAut.conj g).toMonoidHom = E := by
  obtain ⟨g, hgD, hgP⟩ := exists_conj_le_P3 hED hE9
  obtain ⟨d, hdD, hd⟩ := exists_conj_eq_E0_of_le hgP
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9])
  refine ⟨(d * g)⁻¹, twoBD.inv_mem (twoBD.mul_mem hdD hgD), ?_⟩
  have hid : ((MulAut.conj (d * g)⁻¹).toMonoidHom.comp (MulAut.conj d).toMonoidHom).comp
      (MulAut.conj g).toMonoidHom = MonoidHom.id Pm :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  rw [← hd, Subgroup.map_map, Subgroup.map_map, hid, Subgroup.map_id]

end CertificateChecks.KernelG24Th

end
