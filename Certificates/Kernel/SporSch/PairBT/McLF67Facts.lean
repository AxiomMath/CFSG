module

public import Certificates.Kernel.SporSch.PairBT.McLF67Chk
public import Certificates.Kernel.SporSch.PairBT.McLSyl5Chk
public import Certificates.Kernel.SporSch.PairBT.McLSyl5E
public import Certificates.Kernel.SporSch.PairBT.McLSylFactsK
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLF67

open Finset

section Abstract

variable {G : Type*} [Group G]

theorem mem_cent_conj (c x u : G) :
    u ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G) ↔
      c⁻¹ * u * c ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * u * c * x = c⁻¹ * (u * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * u) * c := by rw [h]
      _ = x * (c⁻¹ * u * c) := by group
  · intro h
    calc u * (c * x * c⁻¹) = c * (c⁻¹ * u * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * u * c)) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * u := by group

theorem card_cent_conj (c x : G) :
    Nat.card (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨c⁻¹ * u * c, (mem_cent_conj c x u).1 u.2⟩
      invFun := fun v => ⟨c * v * c⁻¹, (mem_cent_conj c x _).2 ?_⟩
      left_inv := fun u => Subtype.ext ?_
      right_inv := fun v => Subtype.ext ?_ }
  · have e : c⁻¹ * (c * (v : G) * c⁻¹) * c = v := by group
    rw [e]
    exact v.2
  · change c * (c⁻¹ * (u : G) * c) * c⁻¹ = u
    group
  · change c⁻¹ * (c * (v : G) * c⁻¹) * c = v
    group

theorem card_cent_eq {_ : Fintype G} (x : G) {_ : DecidablePred fun g : G => g * x = x * g} :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = #(univ.filter fun g : G => g * x = x * g) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Subgroup.mem_centralizer_singleton_iff)

theorem sq_dvd_cent [Finite G] {p : ℕ} (hp : p.Prime) {a b y : G} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ∉ Subgroup.zpowers a)
    (hay : a * y = y * a) (hby : b * y = y * b) :
    p ^ 2 ∣ Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  refine (CFSG.GH74.GLS.Stage2.Bender.Thm1.sq_dvd_card_closure_pair hp ha hb hab ha1 hb1).trans
    (Subgroup.card_dvd_of_le ?_)
  rw [Subgroup.closure_le]
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.2 hay
  · exact Subgroup.mem_centralizer_singleton_iff.2 hby

theorem sylow_eq_zpowers [Finite G] {p : ℕ} [Fact p.Prime] (hN : ¬p ^ 2 ∣ Nat.card G) {x : G}
    (hx : orderOf x = p) (P : Sylow p G) (hP : Subgroup.zpowers x ≤ P) :
    (P : Subgroup G) = Subgroup.zpowers x := by
  have hzc : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hPc := Sylow.card_eq_multiplicity P
  have hdvd : p ∣ Nat.card P := by
    have h := Subgroup.card_dvd_of_le hP
    rwa [hzc] at h
  have hk : Nat.factorization (Nat.card G) p ≤ 1 := by
    by_contra h
    apply hN
    have h2 : p ^ 2 ∣ Nat.card P := by
      rw [hPc]
      exact pow_dvd_pow p (by omega)
    exact h2.trans (Subgroup.card_subgroup_dvd_card _)
  have hPp : Nat.card P ∣ p := by
    rw [hPc]
    exact (pow_dvd_pow p hk).trans (by rw [pow_one])
  have hPeq : Nat.card P = p := Nat.dvd_antisymm hPp hdvd
  exact (Subgroup.eq_of_le_of_card_ge hP (by rw [hPeq, hzc])).symm

theorem exists_conj_comm [Finite G] {p : ℕ} (hp : p.Prime) (hN : ¬p ^ 2 ∣ Nat.card G) {x y : G}
    (hx : orderOf x = p) (hy : orderOf y = p) :
    ∃ g : G, ∀ u : G, u * (g * x * g⁻¹) = g * x * g⁻¹ * u → u * y = y * u := by
  have := Fact.mk hp
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  have eP := sylow_eq_zpowers hN hx P hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmem : ∀ z : G, z ∈ (Q : Subgroup G) ↔ g⁻¹ * z * g ∈ (P : Subgroup G) := by
    intro z
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hyP := (hmem y).1 (hQ (Subgroup.mem_zpowers y))
  rw [eP] at hyP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyP
  have e : (g * x * g⁻¹) ^ k = y := by
    rw [conj_zpow, hk]
    group
  refine ⟨g, fun u hu => ?_⟩
  have hc : Commute u ((g * x * g⁻¹) ^ k) := Commute.zpow_right hu k
  rw [e] at hc
  exact hc.eq

theorem cent_dvd [Finite G] {p : ℕ} (hp : p.Prime) (hN : ¬p ^ 2 ∣ Nat.card G) {y z : G}
    (hy : orderOf y = p) (hz : orderOf z = p) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) ∣
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨g, hg⟩ := exists_conj_comm hp hN hy hz
  rw [← card_cent_conj g y]
  exact Subgroup.card_dvd_of_le fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.2 (hg u (Subgroup.mem_centralizer_singleton_iff.1 hu))

theorem orderOf_conj_eq (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

theorem triples_three [Finite G] {r₁ r₂ x : G}
    (hcov : ∀ y : G, orderOf y = 5 → IsConj r₁ y ∨ IsConj r₂ y)
    (h₁ : Nat.card (Subgroup.centralizer ({r₁} : Set G)) = 750)
    (h₂ : Nat.card (Subgroup.centralizer ({r₂} : Set G)) = 25) (hxo : orderOf x = 15)
    (hx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 30) {a b y : G} (ha : a ^ 5 = 1)
    (hb : b ^ 5 = 1) (ha1 : a ≠ 1) (hb1 : b ∉ Subgroup.zpowers a) (hy3 : orderOf y = 3)
    (hab : a * b = b * a) (hay : a * y = y * a) (hby : b * y = y * b) : False := by
  have := Fact.mk Nat.prime_five
  have ha5 : orderOf a = 5 := orderOf_eq_prime ha ha1
  have hto : ∀ t u : G, orderOf t = 5 → orderOf u = 3 → u * t = t * u →
      ∃ c, c * r₁ * c⁻¹ = t := by
    intro t u ht hu htu
    rcases hcov t ht with hc | hc
    · exact isConj_iff.1 hc
    · exfalso
      obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      have hm : u ∈ Subgroup.centralizer ({c * r₂ * c⁻¹} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 htu
      have hd := Subgroup.orderOf_dvd_natCard _ hm
      rw [hu, card_cent_conj, h₂] at hd
      norm_num at hd
  obtain ⟨c₁, hc₁⟩ := hto a y ha5 hy3 hay.symm
  have hx6 : orderOf (x ^ 6) = 5 := by
    rw [orderOf_pow' x (by norm_num), hxo]
    norm_num
  have hx10 : orderOf (x ^ 10) = 3 := by
    rw [orderOf_pow' x (by norm_num), hxo]
    norm_num
  have hx15 : x ^ 15 = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  obtain ⟨c₂, hc₂⟩ := hto (x ^ 6) (x ^ 10) hx6 hx10 (by rw [← pow_add, ← pow_add])
  obtain ⟨X, hXd⟩ : ∃ X, X = (c₁ * c₂⁻¹) * x * (c₁ * c₂⁻¹)⁻¹ := ⟨_, rfl⟩
  have hX6 : X ^ 6 = a := by
    rw [hXd, conj_pow, ← hc₂, ← hc₁]
    group
  have hX15 : X ^ 15 = 1 := by
    rw [hXd, conj_pow, hx15]
    group
  have hY3 : orderOf (X ^ 10) = 3 := by
    rw [hXd, conj_pow, orderOf_conj_eq, hx10]
  have hXc : Nat.card (Subgroup.centralizer ({X} : Set G)) = 30 := by
    rw [hXd, card_cent_conj, hx]
  have hH : Nat.card (Subgroup.centralizer ({a} : Set G)) = 750 := by
    rw [← hc₁, card_cent_conj, h₁]
  have hyH : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hay.symm
  have hYH : X ^ 10 ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hX6, ← pow_add, ← pow_add]
  obtain ⟨g, hg⟩ := exists_conj_comm (G := Subgroup.centralizer ({a} : Set G)) Nat.prime_three
    (by rw [hH]; norm_num) (x := ⟨y, hyH⟩) (y := ⟨X ^ 10, hYH⟩)
    (by rw [Subgroup.orderOf_mk, hy3]) (by rw [Subgroup.orderOf_mk, hY3])
  have hca : (g : G) * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hcac : (g : G) * a * (g : G)⁻¹ = a := by
    rw [hca, mul_inv_cancel_right]
  have key : ∀ t : G, t * a = a * t →
      t * ((g : G) * y * (g : G)⁻¹) = (g : G) * y * (g : G)⁻¹ * t → t * X = X * t := by
    intro t hta hty
    have htH : t ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hta
    have h10 : Commute t (X ^ 10) := congrArg Subtype.val (hg ⟨t, htH⟩ (Subtype.ext hty))
    have h6 : Commute t (X ^ 6) := by
      rw [hX6]
      exact hta
    have h16 := h6.mul_right h10
    rw [← pow_add, show 6 + 10 = 15 + 1 from rfl, pow_succ, hX15, one_mul] at h16
    exact h16.eq
  have hka : a * X = X * a := by
    refine key a rfl ?_
    calc a * ((g : G) * y * (g : G)⁻¹) = (g : G) * a * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) := by
          rw [hcac]
      _ = (g : G) * (a * y) * (g : G)⁻¹ := by group
      _ = (g : G) * (y * a) * (g : G)⁻¹ := by rw [hay]
      _ = (g : G) * y * (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) := by group
      _ = (g : G) * y * (g : G)⁻¹ * a := by rw [hcac]
  have hba : (g : G) * b * (g : G)⁻¹ * a = a * ((g : G) * b * (g : G)⁻¹) := by
    calc (g : G) * b * (g : G)⁻¹ * a = (g : G) * b * (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) := by
          rw [hcac]
      _ = (g : G) * (b * a) * (g : G)⁻¹ := by group
      _ = (g : G) * (a * b) * (g : G)⁻¹ := by rw [hab]
      _ = (g : G) * a * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) := by group
      _ = a * ((g : G) * b * (g : G)⁻¹) := by rw [hcac]
  have hkb : (g : G) * b * (g : G)⁻¹ * X = X * ((g : G) * b * (g : G)⁻¹) := by
    refine key _ hba ?_
    calc (g : G) * b * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) = (g : G) * (b * y) * (g : G)⁻¹ := by
          group
      _ = (g : G) * (y * b) * (g : G)⁻¹ := by rw [hby]
      _ = (g : G) * y * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) := by group
  have hb5 : ((g : G) * b * (g : G)⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hb]
    group
  have hbn : (g : G) * b * (g : G)⁻¹ ∉ Subgroup.zpowers a := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hck : (g : G) * a ^ k * (g : G)⁻¹ = a ^ k := by
      rw [(Commute.zpow_right hca k).eq, mul_inv_cancel_right]
    rw [← hck] at hk
    exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨k, mul_left_cancel (mul_right_cancel hk)⟩)
  have hsq := sq_dvd_cent Nat.prime_five ha hb5 hba.symm ha1 hbn hka hkb
  rw [hXc] at hsq
  norm_num at hsq

theorem triples_of_facts [Finite G] (hG : Nat.card G = 898128000) {r₁ r₂ z₇ z₁₁ x : G}
    (hcov : ∀ y : G, orderOf y = 5 → IsConj r₁ y ∨ IsConj r₂ y)
    (h₁ : Nat.card (Subgroup.centralizer ({r₁} : Set G)) = 750)
    (h₂ : Nat.card (Subgroup.centralizer ({r₂} : Set G)) = 25) (ho₇ : orderOf z₇ = 7)
    (h₇ : Nat.card (Subgroup.centralizer ({z₇} : Set G)) = 14) (ho₁₁ : orderOf z₁₁ = 11)
    (h₁₁ : Nat.card (Subgroup.centralizer ({z₁₁} : Set G)) = 11) (hxo : orderOf x = 15)
    (hx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 30) :
    ∀ (r s : ℕ) (a b y : G), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  intro r s a b y hr hs hro hso hrs ha hb hy ha1 hb1 hy1 hab hay hby
  have hfac : Nat.primeFactorsList 898128000 =
      [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 11] := by
    norm_num
  have hmem : ∀ q : ℕ, q.Prime → q ∣ 898128000 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
    intro q hq hd
    have := (Nat.mem_primeFactorsList (by norm_num : (898128000 : ℕ) ≠ 0)).2 ⟨hq, hd⟩
    rw [hfac] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have hsq := sq_dvd_cent hr ha hb hab ha1 hb1 hay hby
  have hr2 : r ^ 2 ∣ 898128000 := by
    rw [← hG]
    exact hsq.trans (Subgroup.card_subgroup_dvd_card _)
  have hr35 : r = 3 ∨ r = 5 := by
    rcases hmem r hr ((dvd_pow_self r two_ne_zero).trans hr2) with h | h | h | h | h
    · subst h
      exact absurd hro (by decide)
    · exact Or.inl h
    · exact Or.inr h
    · subst h
      norm_num at hr2
    · subst h
      norm_num at hr2
  have := Fact.mk hs
  have hys : orderOf y = s := orderOf_eq_prime hy hy1
  have hsd : s ∣ 898128000 := by
    rw [← hG, ← hys]
    exact orderOf_dvd_natCard y
  rcases hmem s hs hsd with rfl | rfl | rfl | rfl | rfl
  · exact absurd hso (by decide)
  · obtain rfl : r = 5 := hr35.resolve_left hrs
    exact triples_three hcov h₁ h₂ hxo hx ha hb ha1 hb1 hys hab hay hby
  · obtain rfl : r = 3 := hr35.resolve_right hrs
    rcases hcov y hys with hc | hc
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₁] at hsq
      norm_num at hsq
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₂] at hsq
      norm_num at hsq
  · have hd := hsq.trans (cent_dvd (by norm_num) (by rw [hG]; norm_num) hys ho₇)
    rw [h₇] at hd
    rcases hr35 with rfl | rfl <;> norm_num at hd
  · have hd := hsq.trans (cent_dvd (by norm_num) (by rw [hG]; norm_num) hys ho₁₁)
    rw [h₁₁] at hd
    rcases hr35 with rfl | rfl <;> norm_num at hd

end Abstract

section McL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairMcL CFSG.Monster.B.Mathieu CertificateChecks.KernelSporSch

theorem img0 : imageList (mclGen 0) = (unpack 275 9 (PMcL.S 0)).toList := by
  rw [mclGen, mclStrongPerm, PMcLCheck.arr_eq 0 (by omega)]
  exact imageList_of_prep (Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr
    (Orb.isInvA_unpack (allN_spec PMcLCheck.perm 0 (by decide)))).1)

theorem img1 : imageList (mclGen 1) = (unpack 275 9 (PMcL.S 1)).toList := by
  rw [mclGen, mclStrongPerm, PMcLCheck.arr_eq 1 (by omega)]
  exact imageList_of_prep (Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr
    (Orb.isInvA_unpack (allN_spec PMcLCheck.perm 1 (by decide)))).1)

theorem card_gen : Nat.card (gen2 (mclGen 0) (mclGen 1)) = 898128000 := by
  rw [chainS_card_proved McLSylFacts.chainS img0 img1 McLSylK.base_nodup, McLSylChk.ord]

open scoped Classical in
theorem mcl_facts : ∃ r₁ r₂ z₇ z₁₁ x : gen2 (mclGen 0) (mclGen 1),
    (∀ y : gen2 (mclGen 0) (mclGen 1), orderOf y = 5 → IsConj r₁ y ∨ IsConj r₂ y) ∧
    Nat.card (Subgroup.centralizer ({r₁} : Set (gen2 (mclGen 0) (mclGen 1)))) = 750 ∧
    Nat.card (Subgroup.centralizer ({r₂} : Set (gen2 (mclGen 0) (mclGen 1)))) = 25 ∧
    orderOf z₇ = 7 ∧
    Nat.card (Subgroup.centralizer ({z₇} : Set (gen2 (mclGen 0) (mclGen 1)))) = 14 ∧
    orderOf z₁₁ = 11 ∧
    Nat.card (Subgroup.centralizer ({z₁₁} : Set (gen2 (mclGen 0) (mclGen 1)))) = 11 ∧
    orderOf x = 15 ∧
    Nat.card (Subgroup.centralizer ({x} : Set (gen2 (mclGen 0) (mclGen 1)))) = 30 := by
  have hQ := McLSylFacts.chainS
  have hnd := McLSylK.base_nodup
  obtain ⟨r₁, hr₁⟩ := chainS_elem_proved hQ img0 img1 hnd McLSyl5Chk.c1 McLSyl5Chk.s1
  obtain ⟨r₂, hr₂⟩ := chainS_elem_proved hQ img0 img1 hnd McLSyl5Chk.c2 McLSyl5Chk.s2
  obtain ⟨z₇, hz₇⟩ := chainS_elem_proved hQ img0 img1 hnd McLF67Chk.c7 McLF67Chk.s7
  obtain ⟨z₁₁, hz₁₁⟩ := chainS_elem_proved hQ img0 img1 hnd McLSylChk.cZ McLSylChk.sZ
  obtain ⟨x, hx⟩ := chainS_elem_proved hQ img0 img1 hnd McLF67Chk.c15 McLF67Chk.s15
  have hc : ∀ (g : gen2 (mclGen 0) (mclGen 1)) (R C : Nat),
      imageList (g : Equiv.Perm (Fin 275)) = (unpack 275 9 R).toList →
      btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI R R = C →
      Nat.card (Subgroup.centralizer ({g} : Set (gen2 (mclGen 0) (mclGen 1)))) = C :=
    fun g R C h1 h2 => by
      rw [← h2, btK_proved hQ img0 img1 hnd (by decide) g g h1 h1]
      exact card_cent_eq g
  have ho : ∀ (g : gen2 (mclGen 0) (mclGen 1)) (R e : Nat),
      imageList (g : Equiv.Perm (Fin 275)) = (unpack 275 9 R).toList →
      canonK 275 9 (mask 9) (275 * 9) R = true →
      ordIs 275 9 (mask 9) (pidn 275 9) R e = true → orderOf g = e + 1 :=
    fun g R e h1 h2 h3 => by
      rw [← Subgroup.orderOf_coe]
      exact ordIs_sound McLSylChk.sz h1 h2 h3
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN : ¬5 ^ (3 + 1) ∣ ordK PMcL.LR 5 := by
    rw [McLSylChk.ord]
    decide
  have hcov := cover_proved McLSylChk.sz hQ hnd img0 img1 (p := 5) (k := 3) (e := 1) rfl
    (by decide) hN (XL := McLS5.XL) rfl McLS5.inc McLS5.he [r₁, r₂] rfl (fun j hj => by
      have hj2 : j < 2 := hj
      interval_cases j
      · exact hr₁
      · exact hr₂)
  refine ⟨r₁, r₂, z₇, z₁₁, x, fun y hy => ?_, hc r₁ _ _ hr₁ McLSyl5Chk.b1,
    hc r₂ _ _ hr₂ McLSyl5Chk.b2, ho z₇ _ 6 hz₇ McLF67Chk.c7 McLF67Chk.o7,
    hc z₇ _ _ hz₇ McLF67Chk.b7, ho z₁₁ _ 10 hz₁₁ McLSylChk.cZ McLSylChk.oZ,
    hc z₁₁ _ _ hz₁₁ McLSylChk.bZZ, ho x _ 14 hx McLF67Chk.c15 McLF67Chk.o15,
    hc x _ _ hx McLF67Chk.b15⟩
  obtain ⟨t, ht, htc⟩ := hcov y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact Or.inl htc
  · exact Or.inr htc

theorem triples_mclP :
    ∀ (r s : ℕ) (a b y : ↥mclP), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  obtain ⟨r₁, r₂, z₇, z₁₁, x, hcov, h₁, h₂, ho₇, h₇, ho₁₁, h₁₁, hxo, hx⟩ := mcl_facts
  exact triples_of_facts card_gen hcov h₁ h₂ ho₇ h₇ ho₁₁ h₁₁ hxo hx

end McL

end CertificateChecks.KernelSporSch.McLF67

end
