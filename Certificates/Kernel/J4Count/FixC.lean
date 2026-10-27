
module

public import Certificates.Kernel.J4Count.FixCBase1

public import Certificates.Kernel.J4Count.FixZ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4FixC CFSG.KD.J4FixC CFSG.KS.SporSch.C11 CFSG.Sporadic.GLQ
open CFSG.Sporadic.SmallF2.Native (vecMulN)
open CFSG.KC.J4Count (combo decode BS PS)
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4NoCK
open CertificateChecks.KernelSporSch.J4Eta CertificateChecks.KernelSporSch.J4NoCP

section Generic

variable {Λ : Type*} [Group Λ] [Finite Λ]

end Generic

section Words

end Words

section Conj

end Conj

section Local

theorem genE_mem {l : ℕ} (hl : l < 7) {g : List ℕ × ℕ} (hg : g ∈ GN l) : genE g ∈ Lj l := by
  obtain ⟨-, h⟩ := fixAllK_spec (CFSG.KS.allN_spec fix_ok l hl) g hg
  refine ⟨genE_mem_H g, ?_⟩
  have e : (genE g)⁻¹ • qv l = qv l := by
    rw [genE, mul_inv_rev, mul_smul, η_inv_self, qv, rv_get hl, walk_sound, η_smul_toRow,
      J4NoCP.etaV_eq, h]
  change genE g • qv l = qv l
  calc genE g • qv l = genE g • ((genE g)⁻¹ • qv l) := by rw [e]
    _ = qv l := smul_inv_smul _ _

theorem gsl_mem {l : ℕ} (hl : l < 7) : ∀ g ∈ gsl l, g ∈ Lj l := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact genE_mem hl hg'

theorem WE_mem {l : ℕ} (hl : l < 7) (w : List ℕ) : WE l w ∈ Lj l := wordE_mem (gsl_mem hl) w

theorem PJ_le {l : ℕ} (hl : l < 7) : PJ l ≤ Lj l := by
  rw [PJ, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact WE_mem hl w

theorem RE_mem {l : ℕ} (hl : l < 7) (r : ℕ) : RE l r ∈ Lj l := WE_mem hl _

theorem PE_closed {l : ℕ} (hl : l < 7) : ∀ u ∈ PE l, ∀ w ∈ PE l, u * w ∈ PE l := by
  intro u hu w hw
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hw
  obtain ⟨q, hq, e⟩ := closedK_spec (CFSG.KS.allN_spec pclosed_ok l hl) (EV l a)
    (List.mem_map.2 ⟨a, ha, rfl⟩) (EV l b) (List.mem_map.2 ⟨b, hb, rfl⟩)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hq
  rw [FixCPair.pairRep_eq (pairRep_mul (WE_rep hl a) (WE_rep hl b)) (WE_rep hl d) e]
  exact List.mem_map.2 ⟨d, hd, rfl⟩

theorem PJ_coe {l : ℕ} (hl : l < 7) (hP : 0 < nth 0 NP l) :
    ((PJ l : Subgroup J) : Set J) = {g | g ∈ PE l} := by
  have := finite_J
  have hne : 0 < (PE l).length := by rw [PE_length hl]; exact hP
  obtain ⟨a, ha⟩ : ∃ a, a ∈ PE l := ⟨_, List.getElem_mem hne⟩
  exact closure_coe_eq ha (PE_closed hl)

theorem card_PJ {l : ℕ} (hl : l < 7) (hP : 0 < nth 0 NP l) : Nat.card (PJ l) = nth 0 NP l := by
  classical
  rw [← SetLike.coe_sort_coe, PJ_coe hl hP, ← PE_length hl, ← List.toFinset_card_of_nodup (PE_nodup hl),
    ← Nat.card_eq_finsetCard]
  congr
  ext g
  simp

theorem CE_mem {l r : ℕ} (hl : l < 7) (hr : r < NR l) :
    ∀ g ∈ CE l r, g ∈ Lj l ⊓ Subgroup.centralizer {RE l r} := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  refine ⟨WE_mem hl w, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h := commK_spec (CFSG.KS.allN_spec (CFSG.KS.allN_spec comm_ok l hl) r hr) (EV l w)
    (List.mem_map.2 ⟨w, hw, rfl⟩)
  exact FixCPair.pairRep_eq (pairRep_mul (WE_rep hl w) (RE_rep hl hr))
    (pairRep_mul (RE_rep hl hr) (WE_rep hl w)) h

theorem TE_mem {l r : ℕ} (hl : l < 7) (hr : r < NR l) (j : ℕ) :
    TE l r j ∈ Lj l ⊓ Subgroup.centralizer {RE l r} :=
  wordE_mem (CE_mem hl hr) _

end Local

section Bound

theorem AF_mem {l r : ℕ} (hl : l < 7) (hr : r < NR l) {a : ℕ} (ha : a ∈ AF l r) :
    η a ∈ Lj l ⊓ Subgroup.centralizer {RE l r} ∧ a < 2048 := by
  have hBS : nth [] BS l = getL BS l := by rw [nth_eq, ← getL_eq, List.getD_eq_getElem?_getD]
  have hPS : nth [] PS l = getL PS l := by rw [nth_eq, ← getL_eq, List.getD_eq_getElem?_getD]
  rw [AF, Finset.mem_filter, Finset.mem_range, bAnd_eq, Bool.and_eq_true] at ha
  obtain ⟨ha, h1, h2⟩ := ha
  rw [hBS, hPS] at h1
  have hfix := (fix_iff_combo hl ha).2 (Nat.eq_of_beq_eq_true h1)
  have e := actsBy_of_pairRep (RE_rep hl hr) a
  rw [app_eq, Nat.eq_of_beq_eq_true h2] at e
  refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨N_le_H (η_mem_N a), hfix⟩,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ha⟩
  calc η a * RE l r = RE l r * η a * (RE l r)⁻¹ * RE l r := by rw [e]
    _ = RE l r * η a := by group

theorem card_cent_ge {l r : ℕ} (hl : l < 7) (hr : r < NR l) :
    nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r ≤
      Nat.card ↥(Lj l ⊓ Subgroup.centralizer {RE l r}) := by
  have := finite_J
  rw [← TL_length hl hr, ← AF_card hl hr, ← Finset.card_range (TL l r).length,
    ← Finset.card_product]
  refine card_le_of_injOn _ _ (fun q => TE l r q.1 * η q.2) (fun q hq => ?_) ?_
  · obtain ⟨-, ha⟩ := Finset.mem_product.1 hq
    exact Subgroup.mul_mem _ (TE_mem hl hr q.1) (AF_mem hl hr ha).1
  · rintro ⟨j, a⟩ hq ⟨j', a'⟩ hq' e1
    change TE l r j * η a = TE l r j' * η a' at e1
    obtain ⟨hj, ha⟩ := Finset.mem_product.1 hq
    obtain ⟨hj', ha'⟩ := Finset.mem_product.1 hq'
    simp only [Finset.mem_range] at hj hj'
    have p1 := pairRep_mul_η (a := a) (TE_rep hl hj)
    have p2 := pairRep_mul_η (a := a') (TE_rep hl hj')
    rw [e1] at p1
    obtain ⟨-, hc⟩ := peqK_spec (FixCPair.peqK_of_eq p1 p2)
    rw [pcK_mkP (Nat.xor_lt_two_pow (paK_lt _) (appK_lt' _ _)),
      pcK_mkP (Nat.xor_lt_two_pow (paK_lt _) (appK_lt' _ _))] at hc
    have hjj : j = j' := by
      by_contra hne
      exact TL_ne hl hr hj hj' hne hc
    subst hjj
    have haa := η_injOn (AF_mem hl hr ha).2 (AF_mem hl hr ha').2 (mul_left_cancel e1)
    simp only at haa
    rw [haa]

theorem sylowP_spec {l : ℕ} (hl : l < 7) {k : ℕ} (hk : nth 0 NP l = 3 ^ k)
    (hidx : ¬ 3 ∣ Nat.card (Lj l) / nth 0 NP l) [Fact (Nat.Prime 3)] [Finite (Lj l)] :
    ∃ P : Sylow 3 (Lj l), ∀ x ∈ (P : Subgroup (Lj l)), (x : J) ∈ PE l := by
  have hpos : 0 < nth 0 NP l := by rw [hk]; positivity
  have hcard := card_PJ hl hpos
  have hP : Nat.card ((PJ l).subgroupOf (Lj l)) = nth 0 NP l := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (PJ_le hl)).toEquiv
  have hpg : IsPGroup 3 ((PJ l).subgroupOf (Lj l)) := IsPGroup.of_card (hP.trans hk)
  have hind : ((PJ l).subgroupOf (Lj l)).index = Nat.card (Lj l) / nth 0 NP l := by
    have e := Subgroup.card_mul_index ((PJ l).subgroupOf (Lj l))
    rw [hP] at e
    rw [← e, Nat.mul_div_cancel_left _ hpos]
  refine ⟨hpg.toSylow (by rw [hind]; exact hidx), fun x hx => ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at hx
  have h2 : (x : J) ∈ ((PJ l : Subgroup J) : Set J) := hx
  rw [PJ_coe hl hpos] at h2
  exact h2

theorem fusion {l : ℕ} (hl : l < 7) {c : J} (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    {x : J} (hx : x ∈ PE l) (hxc : ∃ h ∈ H, h * c * h⁻¹ = x) :
    ∃ r < NR l, ∃ f ∈ Lj l, f * x * f⁻¹ = RE l r := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, hi, hwi⟩ := List.mem_iff_getElem.1 hw
  have hlen := CFSG.KS.allN_spec plen_ok l hl
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hlen
  obtain ⟨h1, h2, -⟩ := hlen
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  rw [PL, List.length_map] at e1
  rw [FL, List.length_map] at e2
  have hiNP : i < nth 0 NP l := e1 ▸ hi
  have hif : i < (nth [] FW l).length := e2 ▸ hiNP
  have ht := CFSG.KS.allN_spec (CFSG.KS.allN_spec tag_ok l hl) i hiNP
  have hp : nth 0 (PL l) i = EV l w := by
    rw [PL, nth_map_of_lt _ _ [] hi, nth_eq, List.getD_eq_getElem _ _ hi, hwi]
  have hf : nth 0 (FL l) i = EV l (nth [] (nth [] FW l) i) := nth_map_of_lt _ _ _ hif
  rw [hp, hf] at ht
  obtain ⟨h, hh, hhx⟩ := hxc
  have hcx := card_cN_conj hh c
  rw [hhx, hcN] at hcx
  rcases tagK_spec ht with ⟨-, hne⟩ | ⟨r, -, he⟩
  · exfalso
    rw [card_centralizer_N_eq (WE_rep hl w), fix_sound (Nat.beq_refl _)] at hcx
    exact hne hcx
  · by_cases hr : r < NR l
    · rw [RL, nth_map_of_lt _ _ [] hr] at he
      refine ⟨r, hr, WE l (nth [] (nth [] FW l) i), WE_mem hl _, ?_⟩
      have e := FixCPair.pairRep_eq (pairRep_mul (WE_rep hl _) (WE_rep hl w))
        (pairRep_mul (WE_rep hl _) (WE_rep hl _)) he
      rw [RE, e]
      group
    · exfalso
      rw [RL, nth_map_ge _ _ _ (not_lt.1 hr)] at he
      have e := FixCPair.pairRep_eq (pairRep_mul (WE_rep hl _) (WE_rep hl w))
        (pairRep_mul pairRep_one (WE_rep hl _)) he
      rw [one_mul, mul_eq_left] at e
      rw [e, centralizer_one, top_inf_eq, card_N] at hcx
      exact absurd hcx (by norm_num)

theorem card_conj_le {l : ℕ} (hl : l < 7) {k : ℕ} (hk : nth 0 NP l = 3 ^ k)
    (hidx : ¬ 3 ∣ Nat.card (Lj l) / nth 0 NP l)
    (hm : ∀ r < NR l, 0 < nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r) {c : J} (hc3 : c ^ 3 = 1)
    (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32) :
    Nat.card {s : Lj l // ∃ h ∈ H, h * c * h⁻¹ = (s : J)} ≤
      ((List.range (NR l)).map fun r =>
        Nat.card (Lj l) / (nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r)).sum := by
  have := finite_J
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := sylowP_spec hl hk hidx
  let reps : List (Lj l) := (List.range (NR l)).map fun r => ⟨RE l r, RE_mem hl r⟩
  have h1 := card_le_sum_classes P (fun s : Lj l => ∃ h ∈ H, h * c * h⁻¹ = (s : J))
    (fun s hs g => by
      obtain ⟨h, hh, e⟩ := hs
      refine ⟨(g : J)⁻¹ * h, H.mul_mem (H.inv_mem (Subgroup.mem_inf.1 g.2).1) hh, ?_⟩
      have e2 : ((g⁻¹ * s * g : Lj l) : J) = (g : J)⁻¹ * (s : J) * (g : J) := by simp
      rw [e2, ← e]
      group)
    (fun s hs => by
      obtain ⟨h, -, e⟩ := hs
      apply Subtype.ext
      have e2 : ((s ^ 3 : Lj l) : J) = (s : J) ^ 3 := by simp
      rw [e2, ← e, conj_pow, hc3, mul_one, mul_inv_cancel]
      simp)
    reps
    (fun x hx hxc => by
      obtain ⟨r, hr, f, hf, e⟩ := fusion hl hcN (hP x hx) hxc
      refine ⟨⟨RE l r, RE_mem hl r⟩, List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩, ?_⟩
      refine isConj_iff.2 ⟨⟨f, hf⟩, Subtype.ext ?_⟩
      have e2 : ((⟨f, hf⟩ * x * (⟨f, hf⟩ : Lj l)⁻¹ : Lj l) : J) = f * (x : J) * f⁻¹ := by simp
      rw [e2, e])
  refine h1.trans (sum_classes_le (Λ := Lj l) (NR l) (fun r => ⟨RE l r, RE_mem hl r⟩)
    (fun r => nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r) hm fun r hr => ?_)
  have h2 := card_centralizer_sub (Lj l) ⟨RE l r, RE_mem hl r⟩
  have h3 := card_cent_ge hl hr
  change nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r ≤
    Nat.card (Subgroup.centralizer ({⟨RE l r, RE_mem hl r⟩} : Set (Lj l)))
  rw [h2]
  exact h3

theorem card_Lj {l : ℕ} (hsz : (orbit H (qv l)).ncard = SZ.getD l 0) :
    Nat.card (Lj l) = 501397585920 / SZ.getD l 0 := by
  have e := Subgroup.card_mul_index (MulAction.stabilizer H (qv l))
  rw [MulAction.index_stabilizer, hsz, card_H'] at e
  have hpos : 0 < SZ.getD l 0 := by
    rw [← hsz]
    exact Set.ncard_pos (Set.finite_range _) |>.2 ⟨qv l, mem_orbit_self _⟩
  rw [card_Lj_stab, ← e, Nat.mul_div_cancel _ hpos]

theorem card_fix_mul_le {l : ℕ} (hl : l < 7) {k : ℕ} (hk : nth 0 NP l = 3 ^ k)
    (hidx : ¬ 3 ∣ Nat.card (Lj l) / nth 0 NP l)
    (hm : ∀ r < NR l, 0 < nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r) {c : J} (hcH : c ∈ H)
    (hc3 : c ^ 3 = 1) (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    (hcC : Nat.card ↥(Subgroup.centralizer {c} ⊓ H) ≤ 34560) :
    Nat.card {x : Row // x ∈ orbit H (qv l) ∧ c • x = x} * Nat.card (Lj l) ≤
      34560 * ((List.range (NR l)).map fun r =>
        Nat.card (Lj l) / (nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r)).sum := by
  have := finite_H
  have e := CFSG.Sporadic.J4.Struct.card_fix_orbit_mul (G := H) (X := Row) (qv l) ⟨c, hcH⟩
  have eC : Nat.card (Subgroup.centralizer ({⟨c, hcH⟩} : Set H)) =
      Nat.card ↥(Subgroup.centralizer {c} ⊓ H) := by
    rw [card_centralizer_sub, inf_comm]
  have eS : Nat.card {s : H // s ∈ MulAction.stabilizer H (qv l) ∧ IsConj ⟨c, hcH⟩ s} =
      Nat.card {s : Lj l // ∃ h ∈ H, h * c * h⁻¹ = (s : J)} :=
    Nat.card_congr
      { toFun := fun s => ⟨⟨s.1.1, Subgroup.mem_inf.2 ⟨s.1.2, s.2.1⟩⟩, by
          obtain ⟨u, hu⟩ := isConj_iff.1 s.2.2
          exact ⟨u.1, u.2, by simpa using congrArg Subtype.val hu⟩⟩
        invFun := fun s => ⟨⟨s.1.1, (Subgroup.mem_inf.1 s.1.2).1⟩, (Subgroup.mem_inf.1 s.1.2).2, by
          obtain ⟨h, hh, e⟩ := s.2
          exact isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext (by simpa using e)⟩⟩
        left_inv := fun s => Subtype.ext (Subtype.ext rfl)
        right_inv := fun s => Subtype.ext (Subtype.ext rfl) }
  rw [eC, eS, ← card_Lj_stab] at e
  change Nat.card {x : Row // x ∈ orbit H (qv l) ∧ c • x = x} * _ = _ at e
  rw [e]
  exact Nat.mul_le_mul hcC (card_conj_le hl hk hidx hm hc3 hcN)

end Bound

section Final

theorem fix_mul_le_of {l : ℕ} (hl : l < 7) (hsz : (orbit H (qv l)).ncard = SZ.getD l 0)
    (L0 k S0 : ℕ) (hL0 : 501397585920 / SZ.getD l 0 = L0) (hk : nth 0 NP l = 3 ^ k)
    (hidx : ¬ 3 ∣ L0 / nth 0 NP l)
    (hm : ∀ r < NR l, 0 < nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r)
    (hS : ((List.range (NR l)).map fun r =>
      L0 / (nth 0 (nth [] NT l) r * nth 0 (nth [] NA l) r)).sum = S0)
    {c : J} (hcH : c ∈ H) (hc3 : c ^ 3 = 1) (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    (hcC : Nat.card ↥(Subgroup.centralizer {c} ⊓ H) ≤ 34560) :
    Nat.card {x : Row // x ∈ orbit H (qv l) ∧ c • x = x} * L0 ≤ 34560 * S0 := by
  have hL : Nat.card (Lj l) = L0 := (card_Lj hsz).trans hL0
  have key := card_fix_mul_le hl hk (by rw [hL]; exact hidx) hm hcH hc3 hcN hcC
  rw [hL, hS] at key
  exact key

theorem card_fix_suborbit_le {l : ℕ} (hl : l < 7) (hsz : (orbit H (qv l)).ncard = SZ.getD l 0)
    {c : J} (hcH : c ∈ H) (hc3 : c ^ 3 = 1) (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    (hcC : Nat.card ↥(Subgroup.centralizer {c} ⊓ H) ≤ 34560) :
    Nat.card {x : Row // x ∈ orbit H (qv l) ∧ c • x = x} ≤ FB.getD l 0 := by
  have hfin : (orbit H (qv l)).Finite := Set.finite_range _
  have : Finite (orbit H (qv l)) := hfin.to_subtype
  have hle : Nat.card {x : Row // x ∈ orbit H (qv l) ∧ c • x = x} ≤ SZ.getD l 0 := by
    rw [← hsz, ← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1, x.2.1⟩ : orbit H (qv l))) fun a b e => ?_
    have e' := congrArg Subtype.val e
    exact Subtype.ext e'
  interval_cases l
  · exact hle
  · have h := fix_mul_le_of (by norm_num) hsz 15360 1 0 (by norm_num [SZ]) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN hcC
    change _ ≤ 0
    omega
  · have h := fix_mul_le_of (by norm_num) hsz 6072 1 0 (by norm_num [SZ]) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN hcC
    change _ ≤ 0
    omega
  · have h := fix_mul_le_of (by norm_num) hsz 9216 2 128 (by norm_num [SZ]) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN hcC
    change _ ≤ 480
    omega
  · have h := fix_mul_le_of (by norm_num) hsz 147456 2 512 (by norm_num [SZ]) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN hcC
    change _ ≤ 120
    omega
  · have h := fix_mul_le_of (by norm_num) hsz 33030144 2 57344 (by norm_num [SZ])
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN
      hcC
    change _ ≤ 60
    omega
  · have h := fix_mul_le_of (by norm_num) hsz 17694720 3 38912 (by norm_num [SZ])
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hcH hc3 hcN
      hcC
    change _ ≤ 76
    omega

theorem card_fix_le_of (hcov : ∀ w ∈ orbit J v, ∃ l < 7, w ∈ orbit H (qv l))
    (hsz : ∀ l < 7, (orbit H (qv l)).ncard = SZ.getD l 0) {c : J} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    (hcC : Nat.card ↥(Subgroup.centralizer {c} ⊓ H) ≤ 34560) :
    Nat.card {w : Row // w ∈ orbit J v ∧ c • w = w} ≤ 737 := by
  classical
  have := finite_J
  have hfinO : (orbit J v).Finite := Set.finite_range _
  set F : Set Row := {w | w ∈ orbit J v ∧ c • w = w}
  set Fl : ℕ → Set Row := fun l => {w | w ∈ orbit H (qv l) ∧ c • w = w}
  have hFl_sub : ∀ l < 7, Fl l ⊆ F := fun l hl w hw => ⟨orbit_H_subset hl hw.1, hw.2⟩
  have hfinF : F.Finite := hfinO.subset fun w hw => hw.1
  have hfinFl : ∀ l < 7, (Fl l).Finite := fun l hl => hfinF.subset (hFl_sub l hl)
  have hU : hfinF.toFinset ⊆ (Finset.range 7).biUnion fun l =>
      if hl : l < 7 then (hfinFl l hl).toFinset else ∅ := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Finset.mem_biUnion, Finset.mem_range]
    obtain ⟨l, hl, hwl⟩ := hcov w hw.1
    exact ⟨l, hl, by rw [dif_pos hl, Set.Finite.mem_toFinset]; exact ⟨hwl, hw.2⟩⟩
  have hcard : ∀ l (hl : l < 7), (hfinFl l hl).toFinset.card ≤ FB.getD l 0 := by
    intro l hl
    rw [← Set.ncard_eq_toFinset_card _ (hfinFl l hl), ← Nat.card_coe_set_eq]
    exact card_fix_suborbit_le hl (hsz l hl) hcH hc3 hcN hcC
  rw [show Nat.card {w : Row // w ∈ orbit J v ∧ c • w = w} = hfinF.toFinset.card by
    rw [← Set.ncard_eq_toFinset_card _ hfinF, ← Nat.card_coe_set_eq]; rfl]
  refine (Finset.card_le_card hU).trans (Finset.card_biUnion_le.trans ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  have c0 := hcard 0 (by norm_num)
  have c1 := hcard 1 (by norm_num)
  have c2 := hcard 2 (by norm_num)
  have c3 := hcard 3 (by norm_num)
  have c4 := hcard 4 (by norm_num)
  have c5 := hcard 5 (by norm_num)
  have c6 := hcard 6 (by norm_num)
  simp only [FB, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3 c4 c5 c6
  simp only [show (0 : ℕ) < 7 by norm_num, show (1 : ℕ) < 7 by norm_num,
    show (2 : ℕ) < 7 by norm_num, show (3 : ℕ) < 7 by norm_num, show (4 : ℕ) < 7 by norm_num,
    show (5 : ℕ) < 7 by norm_num, show (6 : ℕ) < 7 by norm_num, dif_pos]
  omega

theorem fix_eq_of_card (hcov : ∀ w ∈ orbit J v, ∃ l < 7, w ∈ orbit H (qv l))
    (hsz : ∀ l < 7, (orbit H (qv l)).ncard = SZ.getD l 0) {c : J} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    (hcN : Nat.card ↥(Subgroup.centralizer {c} ⊓ N) = 32)
    (hcC : Nat.card ↥(Subgroup.centralizer {c} ⊓ H) ≤ 34560) (S : Finset Row)
    (hS : ∀ p ∈ S, p ∈ orbit J v ∧ c • p = p) (hcard : S.card = 737) :
    (∀ w, w ∈ orbit J v ∧ c • w = w → w ∈ S) ∧
      Nat.card {w : Row // w ∈ orbit J v ∧ c • w = w} = 737 := by
  classical
  have hfinF : {w : Row | w ∈ orbit J v ∧ c • w = w}.Finite :=
    (Set.finite_range _).subset fun w hw => hw.1
  have hle := card_fix_le_of hcov hsz hcH hc3 hcN hcC
  have e : Nat.card {w : Row // w ∈ orbit J v ∧ c • w = w} = hfinF.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfinF, ← Nat.card_coe_set_eq]
    rfl
  have hsub : S ⊆ hfinF.toFinset := fun p hp => by
    rw [Set.Finite.mem_toFinset]
    exact hS p hp
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, ← e]; exact hle)
  refine ⟨fun w hw => ?_, by rw [e, ← heq, hcard]⟩
  rw [heq, Set.Finite.mem_toFinset]
  exact hw

end Final

end CertificateChecks.KernelJ4Count.FixC

end
