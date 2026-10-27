module

public import Certificates.Kernel.SporSch.PairBT.J2F67Chk
public import Certificates.Kernel.SporSch.PairBT.J2F67Syl
public import CFSG.Certificates.Kernel.SporSch.McLSylowProof
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J2F67F

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

theorem exists_conj_comm_pair [Finite G] {r : ℕ} (hr : r.Prime) {a0 b0 : G} (ha : a0 ^ r = 1)
    (hb : b0 ^ r = 1) (hab : a0 * b0 = b0 * a0) (ha1 : a0 ≠ 1) (hb1 : b0 ∉ Subgroup.zpowers a0)
    (hcube : ¬ r ^ 3 ∣ Nat.card G) {a b y : G} (ha' : a ^ r = 1) (hb' : b ^ r = 1)
    (hab' : a * b = b * a) (ha1' : a ≠ 1) (hb1' : b ∉ Subgroup.zpowers a) (hay : a * y = y * a)
    (hby : b * y = y * b) : ∃ g : G, (g⁻¹ * y * g) * a0 = a0 * (g⁻¹ * y * g) := by
  have := Fact.mk hr
  set H := Subgroup.closure ({a, b} : Set G) with hH
  set P0 := Subgroup.closure ({a0, b0} : Set G) with hP0
  have hHsq : r ^ 2 ∣ Nat.card H :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.sq_dvd_card_closure_pair hr ha' hb' hab' ha1' hb1'
  have hP0sq : r ^ 2 ∣ Nat.card P0 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.sq_dvd_card_closure_pair hr ha hb hab ha1 hb1
  have hcardQ : ∀ Q : Sylow r G, Nat.card Q ≤ r ^ 2 := by
    intro Q
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 Q.isPGroup'
    have hdv : r ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup G)
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      exact hcube ((pow_dvd_pow r h).trans hdv)
    rw [hk]
    exact Nat.pow_le_pow_right hr.pos hk2
  obtain ⟨Q0, hQ0⟩ := (CFSG.GH74.GLS.Stage2.Bender.Thm1.isPGroup_closure_pair ha hb hab).exists_le_sylow
  obtain ⟨Q1, hQ1⟩ :=
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.isPGroup_closure_pair ha' hb' hab').exists_le_sylow
  have hP0Q0 : P0 = (Q0 : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ0 ((hcardQ Q0).trans (Nat.le_of_dvd Nat.card_pos hP0sq))
  have hHQ1 : H = (Q1 : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ1 ((hcardQ Q1).trans (Nat.le_of_dvd Nat.card_pos hHsq))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q0 Q1
  have hyc : ∀ x ∈ H, y * x = x * y := by
    intro x hx
    have hle : H ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hay.symm
      · exact hby.symm
    exact Subgroup.mem_centralizer_iff.1 (hle hx) y rfl
  have hconj : ∀ q ∈ (Q0 : Subgroup G), g * q * g⁻¹ ∈ (Q1 : Subgroup G) := by
    intro q hq
    have h1 : MulAut.conj g q ∈ ((g • Q0 : Sylow r G) : Set G) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set hq
    rw [hg] at h1
    exact h1
  have h1 : g * a0 * g⁻¹ ∈ H := by
    rw [hHQ1]
    exact hconj a0 (hP0Q0 ▸ Subgroup.subset_closure (by simp))
  have h2 := hyc _ h1
  refine ⟨g, ?_⟩
  calc g⁻¹ * y * g * a0 = g⁻¹ * (y * (g * a0 * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * a0 * g⁻¹) * y) * g := by rw [h2]
    _ = a0 * (g⁻¹ * y * g) := by group

theorem orderOf_conj_eq (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

theorem triples_of_facts [Finite G] (hG : Nat.card G = 604800) {r₁ r₂ r₃ r₄ z₇ v : G}
    (hcov : ∀ y : G, orderOf y = 5 → IsConj r₁ y ∨ IsConj r₂ y ∨ IsConj r₃ y ∨ IsConj r₄ y)
    (h₁ : Nat.card (Subgroup.centralizer ({r₁} : Set G)) = 50)
    (h₂ : Nat.card (Subgroup.centralizer ({r₂} : Set G)) = 50)
    (h₃ : Nat.card (Subgroup.centralizer ({r₃} : Set G)) = 300)
    (h₄ : Nat.card (Subgroup.centralizer ({r₄} : Set G)) = 300) (ho₇ : orderOf z₇ = 7)
    (h₇ : Nat.card (Subgroup.centralizer ({z₇} : Set G)) = 7) (ho₁ : orderOf r₁ = 5)
    (hv5 : v ^ 5 = 1) (hrv : r₁ * v = v * r₁) (hv : v ∉ Subgroup.zpowers r₁) :
    ∀ (r s : ℕ) (a b y : G), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  intro r s a b y hr hs hro hso hrs ha hb hy ha1 hb1 hy1 hab hay hby
  have hfac : Nat.primeFactorsList 604800 = [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7] := by
    norm_num
  have hmem : ∀ q : ℕ, q.Prime → q ∣ 604800 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
    intro q hq hd
    have := (Nat.mem_primeFactorsList (by norm_num : (604800 : ℕ) ≠ 0)).2 ⟨hq, hd⟩
    rw [hfac] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have hsq := sq_dvd_cent hr ha hb hab ha1 hb1 hay hby
  have hr2 : r ^ 2 ∣ 604800 := by
    rw [← hG]
    exact hsq.trans (Subgroup.card_subgroup_dvd_card _)
  have hr35 : r = 3 ∨ r = 5 := by
    rcases hmem r hr ((dvd_pow_self r two_ne_zero).trans hr2) with h | h | h | h
    · subst h
      exact absurd hro (by decide)
    · exact Or.inl h
    · exact Or.inr h
    · subst h
      norm_num at hr2
  have := Fact.mk hs
  have hys : orderOf y = s := orderOf_eq_prime hy hy1
  have hsd : s ∣ 604800 := by
    rw [← hG, ← hys]
    exact orderOf_dvd_natCard y
  rcases hmem s hs hsd with rfl | rfl | rfl | rfl
  · exact absurd hso (by decide)
  · obtain rfl : r = 5 := hr35.resolve_left hrs
    have hr₁ : r₁ ^ 5 = 1 := by
      rw [← ho₁]
      exact pow_orderOf_eq_one r₁
    have hr₁1 : r₁ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ho₁
      norm_num at ho₁
    obtain ⟨g, hg⟩ := exists_conj_comm_pair Nat.prime_five hr₁ hv5 hrv hr₁1 hv
      (by rw [hG]; norm_num) ha hb hab ha1 hb1 hay hby
    have hm : g⁻¹ * y * g ∈ Subgroup.centralizer ({r₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hg
    have hd := Subgroup.orderOf_dvd_natCard _ hm
    have ho : orderOf (g⁻¹ * y * g) = 3 := by
      have h := orderOf_conj_eq g⁻¹ y
      rwa [inv_inv, hys] at h
    rw [ho, h₁] at hd
    norm_num at hd
  · obtain rfl : r = 3 := hr35.resolve_right hrs
    rcases hcov y hys with hc | hc | hc | hc
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₁] at hsq
      norm_num at hsq
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₂] at hsq
      norm_num at hsq
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₃] at hsq
      norm_num at hsq
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [card_cent_conj, h₄] at hsq
      norm_num at hsq
  · have hd := hsq.trans (cent_dvd (by norm_num) (by rw [hG]; norm_num) hys ho₇)
    rw [h₇] at hd
    rcases hr35 with rfl | rfl <;> norm_num at hd

end Abstract

section J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairJ2 CFSG.Monster.B.Mathieu CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J2F67 CertificateChecks.KernelSporSch.J2F67Chk

theorem img0 : imageList (j2Gen 0) = (unpack 315 9 (PJ2.S 0)).toList := by
  rw [j2Gen, j2StrongPerm, PJ2.arr_eq 0 (by omega)]
  exact imageList_of_prep (Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr
    (Orb.isInvA_unpack (allN_spec PJ2.perm 0 (by decide)))).1)

theorem img1 : imageList (j2Gen 1) = (unpack 315 9 (PJ2.S 1)).toList := by
  rw [j2Gen, j2StrongPerm, PJ2.arr_eq 1 (by omega)]
  exact imageList_of_prep (Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr
    (Orb.isInvA_unpack (allN_spec PJ2.perm 1 (by decide)))).1)

theorem chainS : ChainS 315 9 PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI 7 2 3 PJ2.BP (j2StrongArrs ())
    baseArr PJ2Words.D 40 8 :=
  ⟨PJ2.binds, PJ2.head, PJ2.hl, by norm_num, PJ2.hs⟩

theorem base_nodup : CFSG.Sporadic.Schreier.PairJ2.baseArr.toList.Nodup := by decide

theorem card_gen : Nat.card (gen2 (j2Gen 0) (j2Gen 1)) = 604800 := by
  rw [chainS_card_proved chainS img0 img1 base_nodup, ord]

theorem not_mem_zpowers {u v : Equiv.Perm (Fin 315)} (hu : imageList u = (unpack 315 9 R1).toList)
    (hv : imageList v = (unpack 315 9 V).toList) (hu5 : orderOf u = 5) (hv1 : v ≠ 1) :
    v ∉ Subgroup.zpowers u := by
  classical
  intro hm
  rw [mem_zpowers_iff_mem_range_orderOf, hu5] at hm
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hm
  have h2 := mulK_rep sz hu hu
  have h3 := mulK_rep sz hu h2
  have h4 := mulK_rep sz hu h3
  have key : ∀ P, canonK 315 9 (mask 9) (315 * 9) P = true →
      imageList (u ^ k) = (unpack 315 9 P).toList → (!Nat.beq V P) = true → False :=
    fun P hP h hne => by
      have e : V = P := CFSG.KS.MulH.unpack_injH cV hP (Array.toList_inj.1 (hv.symm.trans h))
      cases hb : Nat.beq V P with
      | false => exact Nat.ne_of_beq_eq_false hb e
      | true =>
        rw [hb] at hne
        exact absurd hne (by decide)
  have hk5 : k < 5 := Finset.mem_range.1 hk
  interval_cases k
  · exact hv1 (pow_zero u)
  · exact key R1 c1 (by rw [pow_one]; exact hu) vne1
  · exact key P2 cP2 (by rw [pow_two]; exact h2) vne2
  · exact key P3 cP3 (by rw [pow_succ', pow_two]; exact h3) vne3
  · exact key P4 cP4 (by rw [pow_succ', pow_succ', pow_two]; exact h4) vne4

open scoped Classical in
theorem j2_facts : ∃ r₁ r₂ r₃ r₄ z₇ v : gen2 (j2Gen 0) (j2Gen 1),
    (∀ y : gen2 (j2Gen 0) (j2Gen 1), orderOf y = 5 →
      IsConj r₁ y ∨ IsConj r₂ y ∨ IsConj r₃ y ∨ IsConj r₄ y) ∧
    Nat.card (Subgroup.centralizer ({r₁} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = 50 ∧
    Nat.card (Subgroup.centralizer ({r₂} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = 50 ∧
    Nat.card (Subgroup.centralizer ({r₃} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = 300 ∧
    Nat.card (Subgroup.centralizer ({r₄} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = 300 ∧
    orderOf z₇ = 7 ∧
    Nat.card (Subgroup.centralizer ({z₇} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = 7 ∧
    orderOf r₁ = 5 ∧ v ^ 5 = 1 ∧ r₁ * v = v * r₁ ∧ v ∉ Subgroup.zpowers r₁ := by
  have hQ := chainS
  have hnd := base_nodup
  obtain ⟨r₁, hr₁⟩ := chainS_elem_proved hQ img0 img1 hnd c1 s1
  obtain ⟨r₂, hr₂⟩ := chainS_elem_proved hQ img0 img1 hnd c2 s2
  obtain ⟨r₃, hr₃⟩ := chainS_elem_proved hQ img0 img1 hnd c3 s3
  obtain ⟨r₄, hr₄⟩ := chainS_elem_proved hQ img0 img1 hnd c4 s4
  obtain ⟨z₇, hz₇⟩ := chainS_elem_proved hQ img0 img1 hnd c7 s7
  obtain ⟨v, hv⟩ := chainS_elem_proved hQ img0 img1 hnd cV sV
  have hc : ∀ (g : gen2 (j2Gen 0) (j2Gen 1)) (R C : Nat),
      imageList (g : Equiv.Perm (Fin 315)) = (unpack 315 9 R).toList → btIs R C = true →
      Nat.card (Subgroup.centralizer ({g} : Set (gen2 (j2Gen 0) (j2Gen 1)))) = C :=
    fun g R C h1 h2 => by
      rw [← btIs_eq h2, btK_proved hQ img0 img1 hnd (by decide) g g h1 h1]
      exact card_cent_eq g
  have ho : ∀ (g : gen2 (j2Gen 0) (j2Gen 1)) (R e : Nat),
      imageList (g : Equiv.Perm (Fin 315)) = (unpack 315 9 R).toList →
      canonK 315 9 (mask 9) (315 * 9) R = true →
      ordIs 315 9 (mask 9) (pidn 315 9) R e = true → orderOf g = e + 1 :=
    fun g R e h1 h2 h3 => by
      rw [← Subgroup.orderOf_coe]
      exact ordIs_sound sz h1 h2 h3
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN : ¬5 ^ (2 + 1) ∣ ordK PJ2.LR 3 := by
    rw [ord]
    decide
  have hcov := cover_proved sz hQ hnd img0 img1 (p := 5) (k := 2) (e := 1) rfl
    (by decide) hN (XL := J2S5.XL) rfl J2S5.inc J2S5.he [r₁, r₂, r₃, r₄] rfl (fun j hj => by
      have hj4 : j < 4 := hj
      interval_cases j
      · exact hr₁
      · exact hr₂
      · exact hr₃
      · exact hr₄)
  have ho₁ : orderOf r₁ = 5 := ho r₁ _ 4 hr₁ c1 o1
  have hov : orderOf v = 5 := ho v _ 4 hv cV oV
  have hrv : r₁ * v = v * r₁ := by
    have e1 := mulK_rep sz hr₁ hv
    have e2 := mulK_rep sz hv hr₁
    rw [comm] at e1
    exact Subtype.ext (imageList_inj (e1.trans e2.symm))
  have hvn : v ∉ Subgroup.zpowers r₁ := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hu5 : orderOf (r₁ : Equiv.Perm (Fin 315)) = 5 := by rw [Subgroup.orderOf_coe, ho₁]
    have hv1 : (v : Equiv.Perm (Fin 315)) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hov
      norm_num at hov
    refine not_mem_zpowers hr₁ hv hu5 hv1 (Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩)
    rw [← Subgroup.coe_zpow, hk]
  refine ⟨r₁, r₂, r₃, r₄, z₇, v, fun y hy => ?_, hc r₁ _ _ hr₁ b1_0, hc r₂ _ _ hr₂ b2_0,
    hc r₃ _ _ hr₃ b3_0, hc r₄ _ _ hr₄ b4_0, ho z₇ _ 6 hz₇ c7 o7, hc z₇ _ _ hz₇ b7_0, ho₁,
    by rw [← hov]; exact pow_orderOf_eq_one v, hrv, hvn⟩
  obtain ⟨t, ht, htc⟩ := hcov y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact Or.inl htc
  · exact Or.inr (Or.inl htc)
  · exact Or.inr (Or.inr (Or.inl htc))
  · exact Or.inr (Or.inr (Or.inr htc))

theorem triples_j2P :
    ∀ (r s : ℕ) (a b y : ↥j2P), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  obtain ⟨r₁, r₂, r₃, r₄, z₇, v, hcov, h₁, h₂, h₃, h₄, ho₇, h₇, ho₁, hv5, hrv, hv⟩ := j2_facts
  exact triples_of_facts card_gen hcov h₁ h₂ h₃ h₄ ho₇ h₇ ho₁ hv5 hrv hv

end J2

end CertificateChecks.KernelSporSch.J2F67F

end
