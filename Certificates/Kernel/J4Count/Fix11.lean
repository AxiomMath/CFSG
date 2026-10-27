
module

public import Certificates.Kernel.J4Count.Fix11Base1

public import Certificates.Kernel.J4Count.Suborb
public import Certificates.Kernel.J4Count.Cent11

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ MulAction
open CFSG.KC.J4Slp CFSG.KS.SporSch.J4B CFSG.KC.J4Q CFSG.KD.J4Q
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch

section Bound

theorem stab_mul_sz (w : Row) :
    Nat.card (stabilizer H w) * (orbit H w).ncard = 501397585920 := by
  have := Subgroup.card_mul_index (stabilizer H w)
  rwa [index_stabilizer, card_H'] at this

theorem fix_cases {h : J} (hh : h ∈ H) (ho : orderOf h = 11) {w : Row} (hw : w ∈ orbit J v)
    (hf : h • w = w) : w = v ∨ (orbit H w).ncard = 82575360 := by
  have hs := ncard_orbit_mem hw
  have hst := stab_mul_sz w
  have h11 : 11 ∣ Nat.card (stabilizer H w) := by
    have hm : (⟨h, hh⟩ : H) ∈ stabilizer H w := hf
    have := Subgroup.orderOf_dvd_natCard (stabilizer H w) hm
    rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, ho] at this
  have hdiv : Nat.card (stabilizer H w) = 501397585920 / (orbit H w).ncard :=
    (Nat.div_eq_of_eq_mul_left (L7_pos _ hs) hst.symm).symm
  rcases eleven_sizes _ hs (hdiv ▸ h11) with e | e
  · left
    have h0 : (orbit H v).ncard = 1 := by
      rw [← qv_zero]
      exact sz_zero
    obtain ⟨g, rfl⟩ := mem_orbit_of_ncard (mem_orbit_self v) hw (e.trans h0.symm)
    have hg : (g : J) ∈ stabilizer J v := by
      rw [stabilizer_v]
      exact g.2
    exact hg
  · exact Or.inr e

theorem card_centralizer_le (hH : H) (ho : orderOf (hH : J) = 11) :
    Nat.card (Subgroup.centralizer ({hH} : Set H)) ≤ 22 := by
  have hc : ∀ y : H, y * hH = hH * y ↔ (y : J) * hH = hH * y := fun y => by
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  have hmap : (Subgroup.centralizer ({hH} : Set H)).map H.subtype =
      Subgroup.centralizer ({(hH : J)} : Set J) ⊓ H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, y.2⟩
      change y ∈ Subgroup.centralizer ({hH} : Set H) at hy
      change (y : J) ∈ Subgroup.centralizer ({(hH : J)} : Set J)
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact (hc y).1 hy
    · rintro ⟨hx, hxH⟩
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      change x ∈ Subgroup.centralizer ({(hH : J)} : Set J) at hx
      change (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer ({hH} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      exact (hc ⟨x, hxH⟩).2 hx
  have key : Nat.card ↥(Subgroup.centralizer ({(hH : J)} : Set J) ⊓ H) ≤ 22 := by
    have hHj : (hH : J) ∈ Hj := by rw [← H_eq_Hj']; exact hH.2
    have := Cent11.card_centralizer_H_eleven_le (hH : J) hHj ho
    rwa [← H_eq_Hj'] at this
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective] at key
  exact key

theorem fix_D_le (hH : H) (ho : orderOf (hH : J) = 11) {q : Row}
    (hq : (orbit H q).ncard = 82575360) :
    Nat.card {x : Row // x ∈ orbit H q ∧ (hH : J) • x = x} ≤ 10 := by
  have : Finite H := finite_H
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hoH : orderOf hH = 11 := by rw [← Subgroup.orderOf_coe]; exact ho
  have e := CFSG.Sporadic.J4.Struct.card_fix_orbit_mul (G := H) q hH
  have hst : Nat.card (stabilizer H q) = 6072 := by
    have := stab_mul_sz q
    rw [hq] at this
    omega
  have hC := card_centralizer_le hH ho
  have P : Sylow 11 (stabilizer H q) := Classical.arbitrary _
  have h1 := CFSG.Sporadic.J4.Struct.card_orderOf_eq_le (L := stabilizer H q) (p := 11)
    (by rw [hst]; norm_num) P
  obtain ⟨hmod, hdvd⟩ := CFSG.Sporadic.J4.Struct.index_normalizer_spec P
  have hidx : (Subgroup.normalizer (P : Set (stabilizer H q))).index ≤ 276 := by
    have hd : (Subgroup.normalizer (P : Set (stabilizer H q))).index ∣ 6072 :=
      hdvd.trans (hst ▸ Subgroup.index_dvd_card _)
    exact idx_le _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hmod
  have hinj : Nat.card {s : H // s ∈ stabilizer H q ∧ IsConj hH s} ≤
      Nat.card {g : stabilizer H q // orderOf g = 11} := by
    refine Nat.card_le_card_of_injective (fun s => ⟨⟨s.1, s.2.1⟩, ?_⟩) ?_
    · rw [← Subgroup.orderOf_coe, Subgroup.coe_mk]
      obtain ⟨c, hc⟩ := isConj_iff.1 s.2.2
      rw [← hc]
      exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective hH).trans hoH
    · intro s t hst'
      exact Subtype.ext
        (congrArg (fun g : {g : stabilizer H q // orderOf g = 11} => ((g.1 : H))) hst')
  have hK : Nat.card {s : H // s ∈ stabilizer H q ∧ IsConj hH s} ≤ 2760 := by
    calc _ ≤ _ := hinj
      _ ≤ (11 - 1) * (Subgroup.normalizer (P : Set (stabilizer H q))).index := h1
      _ ≤ 10 * 276 := Nat.mul_le_mul_left _ hidx
  have hm := Nat.mul_le_mul hC hK
  have e' : Nat.card {x : Row // x ∈ orbit H q ∧ (hH : J) • x = x} * 6072 =
      Nat.card (Subgroup.centralizer ({hH} : Set H)) *
        Nat.card {s : H // s ∈ stabilizer H q ∧ IsConj hH s} := by
    rw [← hst]
    exact e
  omega

theorem card_fix_le_eleven {h : J} (hh : h ∈ H) (ho : orderOf h = 11) :
    Nat.card {w : Row // w ∈ orbit J v ∧ h • w = w} ≤ 11 := by
  classical
  have : Finite H := finite_H
  obtain ⟨l, hl, e⟩ := exists_sz (x := 82575360) (by decide)
  have hsub : {w : Row | w ∈ orbit J v ∧ h • w = w} ⊆
      {v} ∪ {x | x ∈ orbit H (qv l) ∧ h • x = x} := by
    rintro w ⟨hw, hf⟩
    rcases fix_cases hh ho hw hf with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr ⟨mem_orbit_of_ncard (qv_mem hl) hw (hs.trans e.symm), hf⟩
  have hfin : ({v} ∪ {x | x ∈ orbit H (qv l) ∧ h • x = x} : Set Row).Finite :=
    (Set.finite_singleton v).union
      ((Set.finite_range fun g : H => g • qv l).subset fun x hx => hx.1)
  have hD : Nat.card {x : Row // x ∈ orbit H (qv l) ∧ h • x = x} ≤ 10 := fix_D_le ⟨h, hh⟩ ho e
  have e1 : Nat.card {w : Row // w ∈ orbit J v ∧ h • w = w} =
      ({w : Row | w ∈ orbit J v ∧ h • w = w} : Set Row).ncard := Nat.card_coe_set_eq _
  have e2 : Nat.card {x : Row // x ∈ orbit H (qv l) ∧ h • x = x} =
      ({x : Row | x ∈ orbit H (qv l) ∧ h • x = x} : Set Row).ncard := Nat.card_coe_set_eq _
  rw [e1]
  calc _ ≤ ({v} ∪ {x | x ∈ orbit H (qv l) ∧ h • x = x} : Set Row).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ ({v} : Set Row).ncard + ({x | x ∈ orbit H (qv l) ∧ h • x = x} : Set Row).ncard :=
        Set.ncard_union_le _ _
    _ ≤ 1 + 10 := by
        rw [Set.ncard_singleton, ← e2]
        omega
    _ = 11 := rfl

end Bound

section Main

theorem h1_mem : h₁ ∈ H := by
  rw [← stabilizer_v, mem_stabilizer_iff, mul_smul, mul_smul, p1_eq, qx_fix, ← p1_eq, smul_inv_smul]

theorem fixX_eq : fixX = Set.range fun k : Fin 11 => qz ^ (k : ℕ) • p₁ := by
  have hle : fixX.ncard ≤ 11 := by
    have h := card_fix_le_eleven h1_mem orderOf_h1
    rw [← CFSG.Sporadic.J4.Struct.card_fix_conj (orbit J v)
      (fun g x hx => by obtain ⟨k, rfl⟩ := hx; exact ⟨g * k, mul_smul g k v⟩) isConj_qx_h1] at h
    rwa [← Nat.card_coe_set_eq]
  have hsub : (Set.range fun k : Fin 11 => qz ^ (k : ℕ) • p₁) ⊆ fixX := by
    rintro _ ⟨k, rfl⟩
    exact qz_pow_mem k
  have hr : (Set.range fun k : Fin 11 => qz ^ (k : ℕ) • p₁).ncard = 11 := by
    rw [Set.ncard_range_of_injective qz_pow_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : Finite J := KernelJ4Hub.finite_J
  have hfin : fixX.Finite := (Set.finite_range fun g : J => g • v).subset fun w hw => hw.1
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) hfin).symm

theorem card_centralizer_qx' :
    ∃ h ∈ Hj, orderOf h = 11 ∧ Nat.card (Subgroup.centralizer ({qx} : Set J)) =
      11 * Nat.card ↥(Subgroup.centralizer ({h} : Set J) ⊓ Hj) := by
  set g : J := m₁⁻¹ with hgdef
  have hg : g • v = p₁ := p1_eq
  set C : Subgroup J := Subgroup.centralizer ({qx} : Set J) with hC
  have hCmem : ∀ x : J, x ∈ C ↔ x * qx = qx * x := fun x => Subgroup.mem_centralizer_singleton_iff
  have hstab : ∀ x : J, x • p₁ = p₁ ↔ g⁻¹ * x * g ∈ Hj := by
    intro x
    rw [← H_eq_Hj', ← stabilizer_v, mem_stabilizer_iff, mul_smul, mul_smul, hg, inv_smul_eq_iff,
      hg]
  have hh : g⁻¹ * qx * g = h₁ := by rw [hgdef, inv_inv]
  refine ⟨h₁, H_eq_Hj' ▸ h1_mem, orderOf_h1, ?_⟩
  have horb : orbit ↥C p₁ = fixX := by
    ext p
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      have hcc := (hCmem c).1 hc
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := p1_mem
        refine ⟨c * k, ?_⟩
        change (c * k) • v = c • p₁
        rw [mul_smul]
        exact congrArg (c • ·) hk
      · change qx • (c • p₁) = c • p₁
        rw [← mul_smul, ← hcc, mul_smul, qx_fix]
    · intro hp
      rw [fixX_eq] at hp
      obtain ⟨k, rfl⟩ := hp
      exact ⟨⟨qz ^ (k : ℕ), (hCmem _).2 (commute_pow_qz qz_mul_qx k)⟩, rfl⟩
  have hcard : fixX.ncard = 11 := by
    rw [fixX_eq, Set.ncard_range_of_injective qz_pow_inj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hidx := Subgroup.card_mul_index (stabilizer ↥C p₁)
  rw [index_stabilizer, horb, hcard] at hidx
  set D : Subgroup J := C ⊓ stabilizer J p₁ with hD
  have hsub : D.subgroupOf C = stabilizer ↥C p₁ := by
    ext ⟨c, hc⟩
    simp only [hD, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  have hcD : Nat.card ↥(stabilizer ↥C p₁) = Nat.card ↥D := by
    rw [← hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ C)).toEquiv
  have hmap : D.map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({h₁} : Set J) ⊓ Hj := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, hD, mem_stabilizer_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hCmem,
      Subgroup.mem_centralizer_singleton_iff]
    rw [← hh]
    constructor
    · rintro ⟨x, ⟨hxc, hxs⟩, rfl⟩
      refine ⟨?_, (hstab x).1 hxs⟩
      calc g⁻¹ * x * g * (g⁻¹ * qx * g) = g⁻¹ * (x * qx) * g := by group
        _ = g⁻¹ * (qx * x) * g := by rw [hxc]
        _ = g⁻¹ * qx * g * (g⁻¹ * x * g) := by group
    · rintro ⟨hy, hyH⟩
      refine ⟨g * y * g⁻¹, ⟨?_, ?_⟩, by group⟩
      · have e : qx = g * (g⁻¹ * qx * g) * g⁻¹ := by group
        rw [e]
        calc g * y * g⁻¹ * (g * (g⁻¹ * qx * g) * g⁻¹) = g * (y * (g⁻¹ * qx * g)) * g⁻¹ := by
              group
          _ = g * ((g⁻¹ * qx * g) * y) * g⁻¹ := by rw [hy]
          _ = g * (g⁻¹ * qx * g) * g⁻¹ * (g * y * g⁻¹) := by group
      · rw [hstab, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
        exact hyH
  have hcm : Nat.card ↥D = Nat.card ↥(Subgroup.centralizer ({h₁} : Set J) ⊓ Hj) := by
    rw [← hmap]
    have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
    exact (Subgroup.card_map_of_injective hinj).symm
  rw [hcD, hcm] at hidx
  omega

end Main

end CertificateChecks.KernelJ4Count

end
