module

public import Certificates.Kernel.KsEight.CentGlue
public import Certificates.Kernel.KsEight.Syl
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKsEight.SylG8

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut CertificateChecks.KernelKsEight
open CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelCU43Aut.SylG
open CertificateChecks.KernelKsEight.CentG8 CFSG.EvenSporadicStandard.Fin76b

@[expose] def VK (k : Nat) : Prop := k = 0 ∨ k = 2 ∨ k = 5 ∨ k = 7

theorem VK_mul : ∀ a < 8, ∀ b < 8, VK a → VK b → VK (mulD a b) := by
  intro a _ b _ ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    (unfold VK; decide)

theorem VK_sq : ∀ a < 8, VK a → mulD a a = 0 := by unfold VK; decide

theorem VK_comm : ∀ a < 8, ∀ b < 8, VK a → VK b → mulD (mulD a b) a = b := by
  intro a _ b _ ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem mulD8_eq : ∀ a < 8, ∀ b < 8, mulD8 a b = mulD a b := by decide

theorem VK_of_inV {k : Nat} (h : inV k = true) : VK k := by
  unfold inV at h
  simp only [Raw.Orb.bIf_eq] at h
  unfold VK
  split_ifs at h with h0 h2 h5
  · exact Or.inl (Nat.eq_of_beq_eq_true h0)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h5)))
  · exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))

theorem inV_of_VK {k : Nat} (h : VK k) : inV k = true := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl


theorem tP_inv_self {k : Nat} (hk : k < 8) (hV : VK k) : (tP k)⁻¹ = tP k :=
  inv_eq_of_mul_eq_one_right (by rw [tP_mul_eq hk hk, VK_sq k hk hV, tP_zero])

theorem coset_unique {x : Equiv.Perm (Fin 820)} {a b : Nat} (ha : a < 8) (hb : b < 8)
    (h1 : x * (tP a)⁻¹ ∈ P) (h2 : x * (tP b)⁻¹ ∈ P) : a = b := by
  by_contra hne
  apply tP_mul_inv_not_mem ha hb hne
  have e : tP a * (tP b)⁻¹ = (x * (tP a)⁻¹)⁻¹ * (x * (tP b)⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem h1) h2

theorem coset_mul {x y : Equiv.Perm (Fin 820)} {a b : Nat} (ha : a < 8) (hb : b < 8)
    (hx : x * (tP a)⁻¹ ∈ P) (hy : y * (tP b)⁻¹ ∈ P) : x * y * (tP (mulD a b))⁻¹ ∈ P := by
  have hN := (mem_normalizer_iff.1 (tP_mem_normalizer a) _).1 hy
  have e : x * y * (tP (mulD a b))⁻¹ = (x * (tP a)⁻¹) * (tP a * (y * (tP b)⁻¹) * (tP a)⁻¹) *
      (tP a * tP b * (tP (mulD a b))⁻¹) := by group
  rw [e, tP_mul_eq ha hb, mul_inv_cancel, mul_one]
  exact mul_mem hx hN

@[expose] noncomputable def Kv : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := {x | ∃ g ∈ P, ∃ k, k < 8 ∧ VK k ∧ x = g * tP k}
  one_mem' := ⟨1, one_mem _, 0, by norm_num, Or.inl rfl, by rw [tP_zero, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨g, hg, k, hk, hkV, rfl⟩ ⟨g', hg', k', hk', hk'V, rfl⟩
    refine ⟨g * (tP k * g' * (tP k)⁻¹),
      mul_mem hg ((mem_normalizer_iff.1 (tP_mem_normalizer k) g').1 hg'), mulD k k', mulD_lt hk,
      VK_mul k hk k' hk' hkV hk'V, ?_⟩
    rw [← tP_mul_eq hk hk']
    group
  inv_mem' := by
    rintro _ ⟨g, hg, k, hk, hkV, rfl⟩
    refine ⟨tP k * g⁻¹ * (tP k)⁻¹, (mem_normalizer_iff.1 (tP_mem_normalizer k) g⁻¹).1 (inv_mem hg),
      k, hk, hkV, ?_⟩
    rw [inv_mul_cancel_right, mul_inv_rev, tP_inv_self hk hkV]

theorem mem_Kv_of {x : Equiv.Perm (Fin 820)} {k : Nat} (hk : k < 8) (hV : VK k)
    (hx : x * (tP k)⁻¹ ∈ P) : x ∈ Kv :=
  ⟨_, hx, k, hk, hV, by group⟩

theorem coset_of_mem {x : Equiv.Perm (Fin 820)} (hx : x ∈ Kv) :
    ∃ k, k < 8 ∧ VK k ∧ x * (tP k)⁻¹ ∈ P := by
  obtain ⟨g, hg, k, hk, hV, rfl⟩ := hx
  exact ⟨k, hk, hV, by rwa [mul_inv_cancel_right]⟩

theorem Kv_le_R : Kv ≤ R := by
  rintro _ ⟨g, hg, k, hk, -, rfl⟩
  exact mul_mem (P_le_R hg) (tP_mem_R hk)

theorem P_le_Kv : P ≤ Kv := fun x hx => mem_Kv_of (k := 0) (by norm_num) (Or.inl rfl)
  (by rwa [tP_zero, inv_one, mul_one])

theorem conj_coset {x y : Equiv.Perm (Fin 820)} {k : Nat} (hk : k < 8) (hV : VK k)
    (hx : x * (tP k)⁻¹ ∈ P) (hy : y ∈ Kv) : y * x * y⁻¹ * (tP k)⁻¹ ∈ P := by
  obtain ⟨g, hg, m, hm, hmV, rfl⟩ := hy
  have hmk : tP m * tP k * (tP m)⁻¹ = tP k := by
    rw [tP_inv_self hm hmV, tP_mul_eq hm hk, tP_mul_eq (mulD_lt hm) hm, VK_comm m hm k hk hmV hV]
  have hb := (mem_normalizer_iff.1 (tP_mem_normalizer m) _).1 hx
  have hc := (mem_normalizer_iff.1 (tP_mem_normalizer k) g⁻¹).1 (inv_mem hg)
  have e : g * tP m * x * (g * tP m)⁻¹ * (tP k)⁻¹ =
      g * (tP m * (x * (tP k)⁻¹) * (tP m)⁻¹) * (tP m * tP k * (tP m)⁻¹) * g⁻¹ * (tP k)⁻¹ := by
    group
  rw [e, hmk]
  have e2 : g * (tP m * (x * (tP k)⁻¹) * (tP m)⁻¹) * tP k * g⁻¹ * (tP k)⁻¹ =
      g * (tP m * (x * (tP k)⁻¹) * (tP m)⁻¹) * (tP k * g⁻¹ * (tP k)⁻¹) := by group
  rw [e2]
  exact mul_mem (mul_mem hg hb) hc

@[expose] def vK : Fin 4 → ℕ := ![0, 2, 5, 7]

theorem vK_lt (i : Fin 4) : vK i < 8 := by fin_cases i <;> simp [vK]

theorem vK_V (i : Fin 4) : VK (vK i) := by fin_cases i <;> simp [vK, VK]

theorem vK_inj {i i' : Fin 4} (h : vK i = vK i') : i = i' := by
  fin_cases i <;> fin_cases i' <;> simp_all [vK]

@[expose] noncomputable def kvEquiv : (Fin 4 × ↥P) ≃ ↥Kv :=
  Equiv.ofBijective
    (fun p => ⟨(p.2 : Equiv.Perm (Fin 820)) * tP (vK p.1), p.2, p.2.2, vK p.1, vK_lt _, vK_V _, rfl⟩)
    ⟨by
      rintro ⟨i, g⟩ ⟨i', g'⟩ h
      have h1 : (g : Equiv.Perm (Fin 820)) * tP (vK i) = g' * tP (vK i') := congrArg Subtype.val h
      have hii : vK i = vK i' := coset_unique (x := (g : Equiv.Perm (Fin 820)) * tP (vK i))
        (vK_lt i) (vK_lt i') (by rw [mul_inv_cancel_right]; exact g.2)
        (by rw [h1, mul_inv_cancel_right]; exact g'.2)
      obtain rfl := vK_inj hii
      have : (g : Equiv.Perm (Fin 820)) = g' := mul_right_cancel h1
      exact Prod.ext rfl (Subtype.ext this),
    by
      rintro ⟨x, g, hg, k, hk, hkV, rfl⟩
      have : ∃ i : Fin 4, vK i = k := by
        rcases hkV with rfl | rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      obtain ⟨i, rfl⟩ := this
      exact ⟨(i, ⟨g, hg⟩), rfl⟩⟩

theorem card_Kv_pred (Pr : Equiv.Perm (Fin 820) → Prop) :
    Nat.card {x : ↥Kv // Pr x} =
      Nat.card {g : ↥P // Pr (g * tP 0)} + Nat.card {g : ↥P // Pr (g * tP 2)} +
        Nat.card {g : ↥P // Pr (g * tP 5)} + Nat.card {g : ↥P // Pr (g * tP 7)} := by
  let q : Fin 4 × ↥P → Prop := fun p => Pr ((kvEquiv p : ↥Kv) : Equiv.Perm (Fin 820))
  have e1 : {x : ↥Kv // Pr x} ≃ {p : Fin 4 × ↥P // q p} :=
    Equiv.subtypeEquiv kvEquiv.symm (fun x => by simp [q])
  have e2 : {p : Fin 4 × ↥P // q p} ≃ Σ i : Fin 4, {g : ↥P // Pr (g * tP (vK i))} :=
    Equiv.subtypeProdEquivSigmaSubtype (fun (i : Fin 4) (g : ↥P) =>
      Pr ((kvEquiv (i, g) : ↥Kv) : Equiv.Perm (Fin 820)))
  rw [Nat.card_congr (e1.trans e2), Nat.card_sigma, Fin.sum_univ_four]
  simp [vK]

theorem card_Kv : Nat.card Kv = 4 * 3265920 := by
  rw [← Nat.card_congr kvEquiv, Nat.card_prod, card_P]
  simp

theorem card_centKv {j : Nat} (hj : j < 8) :
    Nat.card (centralizerIn Kv (rK j)) = centKs ks8Reps[j]! := by
  have e : Nat.card (centralizerIn Kv (rK j)) =
      Nat.card {x : ↥Kv // (x : Equiv.Perm (Fin 820)) * rK j = rK j * x} :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
        invFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2 y.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hr := rep_ks hj
  rw [e, card_Kv_pred (fun x => x * rK j = rK j * x), ← count_coset hr, ← count_coset hr,
    ← count_coset hr, ← count_coset hr]
  simp only [centKs, vIxL, List.foldl_cons, List.foldl_nil, zero_add]

theorem card_centKv' {j : Nat} (hj : j < 8) : Nat.card (centralizerIn Kv (rK j)) =
    4 * Nat.card ↥(P ⊓ centralizer ({rK j} : Set (Equiv.Perm (Fin 820)))) := by
  rw [card_centKv hj, centKs_eq hj]

theorem conjClass_conj {H : Subgroup (Equiv.Perm (Fin 820))} {a c : Equiv.Perm (Fin 820)}
    (hc : c ∈ H) : conjClass H (c * a * c⁻¹) = conjClass H a := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, mul_mem hd (inv_mem hc), by group⟩

theorem cent_card_conj {H : Subgroup (Equiv.Perm (Fin 820))} {a c : Equiv.Perm (Fin 820)}
    (hc : c ∈ H) : Nat.card (centralizerIn H (c * a * c⁻¹)) = Nat.card (centralizerIn H a) := by
  have h1 := ncard_conjClass_mul_card H (c * a * c⁻¹)
  have h2 := ncard_conjClass_mul_card H a
  rw [conjClass_conj hc] at h1
  have hpos : 0 < (conjClass H a).ncard :=
    (Set.ncard_pos (conjClass_finite H a)).2 ⟨a, 1, one_mem _, by group⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem disjoint_of_ncard {H : Subgroup (Equiv.Perm (Fin 820))} {a b : Equiv.Perm (Fin 820)}
    (h : (conjClass H a).ncard ≠ (conjClass H b).ncard) : Disjoint (conjClass H a) (conjClass H b) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ ⟨d, hd, e⟩
  apply h
  have e1 := conjClass_conj (a := a) hc
  have e2 := conjClass_conj (a := b) hd
  rw [← e1, ← e2, e]

theorem tau_coset {l : Nat} (hl : l < 7) : genLab l < 8 ∧ tau l * (tP (genLab l))⁻¹ ∈ P := by
  by_cases h5 : l < 5
  · have hg : genLab l = 0 := by interval_cases l <;> rfl
    obtain ⟨γ, hγ, hγP⟩ := mem_P (gen_facts hl).1 (allN_spec in_facts.1 l h5)
    have e := pr_eq (tau_spec hl).1 hγ rfl
    rw [hg, tP_zero, inv_one, mul_one, e]
    exact ⟨by norm_num, hγP⟩
  · rcases (by omega : l = 5 ∨ l = 6) with rfl | rfl
    · have hg : genLab 5 = 1 := rfl
      rw [hg, tP_one]
      exact ⟨by norm_num, (tau_spec (j := 5) (by norm_num)).2.2.1 rfl⟩
    · have hg : genLab 6 = 4 := rfl
      rw [hg, tP_four]
      exact ⟨by norm_num, (tau_spec (j := 6) (by norm_num)).2.2.2 rfl⟩

theorem lab_spec : ∀ i < 1024, LB i < 8 ∧ xT i * (tP (LB i))⁻¹ ∈ P := by
  have hlab := ksLab
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hlab
  obtain ⟨h0, hs⟩ := hlab
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [Nat.eq_of_beq_eq_true h0, xT_zero, tP_zero, inv_one, mul_one]
      exact ⟨by norm_num, one_mem _⟩
    · obtain ⟨h1, h2, h3, -⟩ := (penumPt_specH (pe i (by rw [hcnt]; exact hi))).2.1 (by omega)
      have ex : xT i = xT (parOf TS.PL i) * tau (labOf TS.PL i) := by
        refine pr_eq (pr_xT hi) ?_ rfl
        rw [h3]
        exact pr_step h2 (pr_xT (by omega))
      have hd := Raw.Orb.allN_iff.1 hs (i - 1) (by omega)
      rw [Raw.Orb.strictB_eq, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos] at hd
      obtain ⟨ha, hpa⟩ := ih _ h1 (by omega)
      obtain ⟨hb, htb⟩ := tau_coset h2
      rw [Nat.eq_of_beq_eq_true hd, mulD8_eq _ ha _ hb, ex]
      exact ⟨mulD_lt ha, coset_mul ha hb hpa htb⟩

theorem xT_mem_Kv {i : Nat} (hi : i < 1024) (h : inV (LB i) = true) : xT i ∈ Kv :=
  mem_Kv_of (lab_spec i hi).1 (VK_of_inV h) (lab_spec i hi).2

@[expose] noncomputable def Sg : Subgroup (Equiv.Perm (Fin 820)) := Tg ⊓ Kv

theorem card_Sg : Nat.card Sg = 512 := by
  classical
  let F : Finset Nat := (Finset.range 1024).filter fun i => inV (LB i) = true
  have hF : F.card = 512 := by
    have h := ksCnt
    rw [foldUp_count] at h
    exact Nat.eq_of_beq_eq_true h
  have hmem : ∀ i ∈ F, xT i ∈ Sg := fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
    have h1' := Finset.mem_range.1 h1
    exact mem_inf.2 ⟨(mem_Tg _).2 ⟨i, h1', rfl⟩, xT_mem_Kv h1' h2⟩
  let f : ↥F → ↥Sg := fun i => ⟨xT i, hmem i i.2⟩
  have hb : Function.Bijective f := by
    refine ⟨fun a b e => Subtype.ext (xT_inj a (Finset.mem_range.1 (Finset.mem_filter.1 a.2).1) b
      (Finset.mem_range.1 (Finset.mem_filter.1 b.2).1) (congrArg Subtype.val e)), fun y => ?_⟩
    obtain ⟨hyT, hyK⟩ := mem_inf.1 y.2
    obtain ⟨i, hi, e⟩ := (mem_Tg _).1 hyT
    obtain ⟨k, hk, hV, hkP⟩ := coset_of_mem hyK
    have hk' := coset_unique (x := (y : Equiv.Perm (Fin 820))) (lab_spec i hi).1 hk
      (by rw [← e]; exact (lab_spec i hi).2) hkP
    refine ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_⟩⟩, Subtype.ext e⟩
    rw [hk']
    exact inV_of_VK hV
  rw [← Nat.card_congr (Equiv.ofBijective f hb), Nat.card_eq_finsetCard, hF]

theorem conj_two_group {H : Subgroup (Equiv.Perm (Fin 820))} (hH : H ≤ R) {n : ℕ}
    (hc : Nat.card H = 2 ^ n) : ∃ y ∈ R, ∀ h ∈ H, y⁻¹ * h * y ∈ Tg := by
  have hcard : Nat.card (Tg.subgroupOf R) = 2 ^ (Nat.card R).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le_R).toEquiv, card_Tg, card_R', fact2]
    norm_num
  let S : Sylow 2 R := Sylow.ofCard (Tg.subgroupOf R) hcard
  have hZ : IsPGroup 2 (H.subgroupOf R) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hc])
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hZ
  obtain ⟨g, hg⟩ := exists_conj_sylow S Q
  refine ⟨g, g.2, fun h hh => ?_⟩
  have hXQ : (⟨h, hH hh⟩ : R) ∈ (Q : Subgroup R) := hQ (by rw [mem_subgroupOf]; exact hh)
  have hm := (hg ⟨h, hH hh⟩).1 hXQ
  have hS : ((S : Subgroup R)) = Tg.subgroupOf R := rfl
  rw [hS, mem_subgroupOf] at hm
  simpa using hm

theorem conj_two_group_P {H : Subgroup (Equiv.Perm (Fin 820))} (hH : H ≤ R) {n : ℕ}
    (hc : Nat.card H = 2 ^ n) : ∃ p ∈ P, ∀ h ∈ H, p⁻¹ * h * p ∈ Tg := by
  obtain ⟨y, hy, hyT⟩ := conj_two_group hH hc
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hy
  obtain ⟨s, hs, hsP⟩ := coset_rep hk
  refine ⟨g * tP k * s⁻¹, ?_, fun h hh => ?_⟩
  · have e : g * tP k * s⁻¹ = g * (s * (tP k)⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hg (inv_mem hsP)
  · have e : (g * tP k * s⁻¹)⁻¹ * h * (g * tP k * s⁻¹) =
        s * ((g * tP k)⁻¹ * h * (g * tP k)) * s⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hs (hyT h hh)) (inv_mem hs)

theorem testBit_fold (f : Nat → Nat) : ∀ (n i : Nat),
    ((List.range n).foldl (fun M q => Nat.lor M (Nat.shiftLeft 1 (f q))) 0).testBit i = true →
      ∃ q < n, f q = i := by
  intro n
  induction n with
  | zero => intro i h; simp at h
  | succ n ih =>
    intro i h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    have e : ∀ a b : Nat, Nat.lor a (Nat.shiftLeft 1 b) = a ||| 2 ^ b := fun a b => by
      rw [← Nat.one_shiftLeft]
      rfl
    rw [e, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨q, hq, e⟩ := ih i h
      exact ⟨q, by omega, e⟩
    · exact ⟨n, by omega, of_decide_eq_true h⟩

theorem fourK_all : ∀ i < 1024, fourK i = true := by
  intro i hi
  have hs : ∀ s < 8, ∀ d < 128, fourK (128 * s + d) = true := by
    intro s hs d hd
    interval_cases s
    · rw [(by omega :128 * 0 + d = d)]; exact Raw.Orb.allN_iff.1 ksF0 d hd
    · rw [(by omega :128 * 1 + d = 128 + d)]; exact Raw.Orb.allN_iff.1 ksF1 d hd
    · rw [(by omega :128 * 2 + d = 256 + d)]; exact Raw.Orb.allN_iff.1 ksF2 d hd
    · rw [(by omega :128 * 3 + d = 384 + d)]; exact Raw.Orb.allN_iff.1 ksF3 d hd
    · rw [(by omega :128 * 4 + d = 512 + d)]; exact Raw.Orb.allN_iff.1 ksF4 d hd
    · rw [(by omega :128 * 5 + d = 640 + d)]; exact Raw.Orb.allN_iff.1 ksF5 d hd
    · rw [(by omega :128 * 6 + d = 768 + d)]; exact Raw.Orb.allN_iff.1 ksF6 d hd
    · rw [(by omega :128 * 7 + d = 896 + d)]; exact Raw.Orb.allN_iff.1 ksF7 d hd
  have e : i = 128 * (i / 128) + i % 128 := (Nat.div_add_mod i 128).symm
  rw [e]
  exact hs _ (by omega) _ (by omega)

theorem swK_all : ∀ q < 224, swK q = true := by
  intro q hq
  have hs : ∀ s < 7, ∀ d < 32, swK (32 * s + d) = true := by
    intro s hs d hd
    interval_cases s
    · rw [(by omega :32 * 0 + d = d)]; exact Raw.Orb.allN_iff.1 ksSW0 d hd
    · rw [(by omega :32 * 1 + d = 32 + d)]; exact Raw.Orb.allN_iff.1 ksSW1 d hd
    · rw [(by omega :32 * 2 + d = 64 + d)]; exact Raw.Orb.allN_iff.1 ksSW2 d hd
    · rw [(by omega :32 * 3 + d = 96 + d)]; exact Raw.Orb.allN_iff.1 ksSW3 d hd
    · rw [(by omega :32 * 4 + d = 128 + d)]; exact Raw.Orb.allN_iff.1 ksSW4 d hd
    · rw [(by omega :32 * 5 + d = 160 + d)]; exact Raw.Orb.allN_iff.1 ksSW5 d hd
    · rw [(by omega :32 * 6 + d = 192 + d)]; exact Raw.Orb.allN_iff.1 ksSW6 d hd
  have e : q = 32 * (q / 32) + q % 32 := (Nat.div_add_mod q 32).symm
  rw [e]
  exact hs _ (by omega) _ (by omega)

theorem ls_spec {q : Nat} (hq : q < 224) : LS q < 1024 ∧ inV (LB (LS q)) = true ∧
    (q < 223 → LS q < LS (q + 1)) := by
  have h := Raw.Orb.allN_iff.1 ksLS q hq
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true,
    Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [Raw.Orb.bIf_eq] at h3
  refine ⟨h1, h2, fun hq' => ?_⟩
  rw [if_pos (Nat.blt_eq.mpr hq'), Nat.blt_eq] at h3
  exact h3

theorem ls_mono : ∀ a b, a < b → b < 224 → LS a < LS b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact (ih h (by omega)).trans ((ls_spec (by omega)).2.2 (by omega))
    · exact (ls_spec (by omega)).2.2 (by omega)

theorem pw_spec {c : Nat} (hc : c < 14) : CRQ c < 224 ∧ CJP c < 8 ∧ ∃ γ ∈ P,
    γ * rK (CJP c) * γ⁻¹ = xT (LS (CRQ c)) := by
  have h := Raw.Orb.allN_iff.1 ksPW c hc
  unfold pwK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P h3 h4
  have hl := (ls_spec h1).1
  have e := pr_eq (pr_pc hγ (rK_spec h2).1) (pr_pc (pr_xT hl) hγ) (Nat.eq_of_beq_eq_true h5)
  refine ⟨h1, h2, γ, hγP, ?_⟩
  calc γ * rK (CJP c) * γ⁻¹ = xT (LS (CRQ c)) * γ * γ⁻¹ := by rw [e]
    _ = _ := by group

theorem sw_spec {q : Nat} (hq : q < 224) : SWI q < 1024 ∧ inV (LB (SWI q)) = true ∧
    SCL q < 14 ∧ xT (LS q) = xT (SWI q) * xT (LS (CRQ (SCL q))) * (xT (SWI q))⁻¹ := by
  have h := swK_all q hq
  unfold swK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl := (ls_spec (pw_spec h3).1).1
  have e := pr_eq (pr_pc (pr_xT h1) (pr_xT hl)) (pr_pc (pr_xT (ls_spec hq).1) (pr_xT h1))
    (Nat.eq_of_beq_eq_true h4)
  refine ⟨h1, h2, h3, ?_⟩
  calc xT (LS q) = xT (LS q) * xT (SWI q) * (xT (SWI q))⁻¹ := by group
    _ = _ := by rw [← e]

theorem listed {i : Nat} (hi : i < 1024) (hV : inV (LB i) = true) (h4 : xT i ^ 4 ≠ 1) :
    ∃ q < 224, LS q = i := by
  have h := fourK_all i hi
  unfold fourK at h
  rw [Raw.Orb.bIf_eq, if_pos hV, Raw.Orb.bIf_eq] at h
  split_ifs at h with hb
  · rw [Raw.Orb.hasBit_eq, ← Nat.eq_of_beq_eq_true ksLM, Raw.Orb.foldUp_eq] at hb
    exact testBit_fold LS 224 i hb
  · rw [Raw.Orb.strictB_eq] at h
    have hp := pr_pc (pr_pc (pr_xT hi) (pr_xT hi)) (pr_pc (pr_xT hi) (pr_xT hi))
    have e := pr_eq hp pr_pidn (Nat.eq_of_beq_eq_true h)
    have n4 : (4 : Nat) = 2 * 2 := rfl
    exact absurd (by rw [n4, pow_mul, pow_two, pow_two]; exact e) h4

theorem orderOf_rK {j : Nat} (hj : j < 8) : orderOf (rK j) = 8 := by
  obtain ⟨-, -, h8, h4⟩ := rK_spec hj
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)
  simpa using this

theorem listed_conj {q : Nat} (hq : q < 224) : CJP (SCL q) < 8 ∧ ∃ u ∈ Kv,
    xT (LS q) = u * rK (CJP (SCL q)) * u⁻¹ := by
  obtain ⟨ht, htV, hc, e⟩ := sw_spec hq
  obtain ⟨-, hj, γ, hγP, e2⟩ := pw_spec hc
  refine ⟨hj, xT (SWI q) * γ, mul_mem (xT_mem_Kv ht htV) (P_le_Kv hγP), ?_⟩
  rw [e, ← e2]
  group

theorem ksC2_facts : ((Finset.range 14).filter fun c => CJP c = 2).card = 1 ∧
    ((Finset.range 224).filter fun q => CJP (SCL q) = 2).card = 32 := by
  have h := ksC2
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, foldUp_count, foldUp_count] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  refine ⟨?_, ?_⟩
  · rw [← e1]
    congr 1
  · rw [← e2]
    congr 1

theorem card_two : Nat.card ↥(P ⊓ centralizer ({rK 2} : Set (Equiv.Perm (Fin 820)))) = 4 := by
  classical
  obtain ⟨h48, -⟩ := card_cent_two
  have hK := card_centKv' (j := 2) (by norm_num)
  set C := centralizerIn Kv (rK 2) with hC
  have hCR : C ≤ R := fun x hx => Kv_le_R (mem_inf.1 hx).1
  have hpow : ∃ n, Nat.card C = 2 ^ n := by
    rcases h48 with h | h
    · exact ⟨4, by rw [hK, h]; norm_num⟩
    · exact ⟨5, by rw [hK, h]; norm_num⟩
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨p, hpP, hpT⟩ := conj_two_group_P hCR hn
  have hr2C : rK 2 ∈ C := mem_inf.2 ⟨mem_Kv_of (k := 5) (by norm_num) (Or.inr (Or.inr (Or.inl rfl)))
    (rK_spec (j := 2) (by norm_num)).2.1, mem_centralizer_singleton_iff.2 rfl⟩
  set x := p⁻¹ * rK 2 * p with hx
  have hxS : x ∈ Sg := by
    refine mem_inf.2 ⟨hpT _ hr2C, ?_⟩
    exact mul_mem (mul_mem (inv_mem (P_le_Kv hpP)) (mem_inf.1 hr2C).1) (P_le_Kv hpP)
  have hle : Nat.card C ≤ Nat.card (centralizerIn Sg x) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨p⁻¹ * c.1 * p, mem_inf.2 ⟨mem_inf.2
      ⟨hpT _ c.2, mul_mem (mul_mem (inv_mem (P_le_Kv hpP)) (mem_inf.1 c.2).1) (P_le_Kv hpP)⟩,
      mem_centralizer_singleton_iff.2 ?_⟩⟩) ?_
    · have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2
      calc p⁻¹ * c.1 * p * x = p⁻¹ * (c.1 * rK 2) * p := by rw [hx]; group
        _ = p⁻¹ * (rK 2 * c.1) * p := by rw [hc]
        _ = x * (p⁻¹ * c.1 * p) := by rw [hx]; group
    · intro a b e
      have e' : p⁻¹ * a.1 * p = p⁻¹ * b.1 * p := congrArg (fun y => y.1) e
      exact Subtype.ext (by simpa using e')
  obtain ⟨i, hi, hxi⟩ := (mem_Tg x).1 (mem_inf.1 hxS).1
  have hxc : x * (tP 5)⁻¹ ∈ P := by
    have := conj_coset (k := 5) (y := p⁻¹) (by norm_num) (Or.inr (Or.inr (Or.inl rfl)))
      (rK_spec (j := 2) (by norm_num)).2.1 (inv_mem (P_le_Kv hpP))
    rwa [inv_inv] at this
  have hLB : LB i = 5 := coset_unique (lab_spec i hi).1 (by norm_num) (lab_spec i hi).2
    (by rw [hxi]; exact hxc)
  have hx4 : xT i ^ 4 ≠ 1 := by
    have hcp : (p⁻¹ * rK 2 * p) ^ 4 = p⁻¹ * rK 2 ^ 4 * p := by
      have := conj_pow (a := p⁻¹) (b := rK 2) (i := 4)
      simpa using this
    rw [hxi, hx, hcp]
    intro e
    apply (rK_spec (j := 2) (by norm_num)).2.2.2
    have := congrArg (fun y => p * y * p⁻¹) e
    simpa [mul_assoc] using this
  obtain ⟨q, hq, hqi⟩ := listed hi (by rw [hLB]; rfl) hx4
  obtain ⟨hj', u, hu, hxu⟩ := listed_conj hq
  set j' := CJP (SCL q) with hj'def
  have hj2 : j' = 2 := by
    have hcK : Nat.card (centralizerIn Kv (rK j')) = Nat.card C := by
      have e : rK 2 = (p * u) * rK j' * (p * u)⁻¹ := by
        have : x = u * rK j' * u⁻¹ := by rw [← hxu, hqi, hxi]
        calc rK 2 = p * x * p⁻¹ := by rw [hx]; group
          _ = _ := by rw [this]; group
      rw [hC, e, cent_card_conj (mul_mem (P_le_Kv hpP) hu)]
    have hco : ks8Coset[j']! = 5 := by
      have hm : rK j' = (p * u)⁻¹ * rK 2 * (p * u)⁻¹⁻¹ := by
        have : x = u * rK j' * u⁻¹ := by rw [← hxu, hqi, hxi]
        rw [inv_inv]
        calc rK j' = u⁻¹ * x * u := by rw [this]; group
          _ = _ := by rw [hx]; group
      have h1 := conj_coset (k := 5) (y := (p * u)⁻¹) (by norm_num) (Or.inr (Or.inr (Or.inl rfl)))
        (rK_spec (j := 2) (by norm_num)).2.1 (inv_mem (mul_mem (P_le_Kv hpP) hu))
      rw [← hm] at h1
      exact coset_unique (coset_lt j' hj') (by norm_num) (rK_spec hj').2.1 h1
    have hcases : j' = 2 ∨ j' = 3 ∨ j' = 4 := by
      have key : ∀ j < 8, ks8Coset[j]! = 5 → j = 2 ∨ j = 3 ∨ j = 4 := by decide
      exact key j' hj' hco
    rcases hcases with h | h | h
    · exact h
    · exfalso
      rw [h, card_centKv' (by norm_num), card_cent3] at hcK
      rcases h48 with h' | h' <;> rw [hK, h'] at hcK <;> omega
    · exfalso
      rw [h, card_centKv' (by norm_num), card_cent4] at hcK
      rcases h48 with h' | h' <;> rw [hK, h'] at hcK <;> omega
  obtain ⟨hF1, hF2⟩ := ksC2_facts
  obtain ⟨c0, hc0⟩ := Finset.card_eq_one.1 hF1
  have huniq : ∀ q' < 224, CJP (SCL q') = 2 → SCL q' = c0 := by
    intro q' hq' h
    have hm : SCL q' ∈ (Finset.range 14).filter fun c => CJP c = 2 :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (sw_spec hq').2.2.1, h⟩
    rw [hc0] at hm
    exact Finset.mem_singleton.1 hm
  set xc := xT (LS (CRQ c0)) with hxcdef
  have hsub : (((Finset.range 224).filter fun q => CJP (SCL q) = 2).image fun q => xT (LS q) :
      Set (Equiv.Perm (Fin 820))) ⊆ conjClass Sg xc := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨q', hq', rfl⟩ := hy
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq')
    have hq1' := Finset.mem_range.1 hq1
    obtain ⟨ht, htV, -, e⟩ := sw_spec hq1'
    refine ⟨xT (SWI q'), mem_inf.2 ⟨(mem_Tg _).2 ⟨_, ht, rfl⟩, xT_mem_Kv ht htV⟩, ?_⟩
    beta_reduce
    rw [e, huniq q' hq1' hq2]
  have hinj : Set.InjOn (fun q => xT (LS q)) ↑((Finset.range 224).filter fun q => CJP (SCL q) = 2) := by
    intro a ha b hb e
    have ha' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1
    have hb' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1
    have e2 := xT_inj _ (ls_spec ha').1 _ (ls_spec hb').1 e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e2 (ls_mono a b h hb').ne
    · exact absurd e2 (ls_mono b a h ha').ne'
  have h32 : 32 ≤ (conjClass Sg xc).ncard := by
    have := Set.ncard_le_ncard hsub (conjClass_finite Sg xc)
    rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hF2] at this
  have hxc16 : Nat.card (centralizerIn Sg xc) ≤ 16 := by
    have h := ncard_conjClass_mul_card Sg xc
    rw [card_Sg] at h
    nlinarith
  have hxx : Nat.card (centralizerIn Sg x) = Nat.card (centralizerIn Sg xc) := by
    obtain ⟨ht, htV, -, e⟩ := sw_spec hq
    have : x = xT (SWI q) * xc * (xT (SWI q))⁻¹ := by
      rw [← hxi, ← hqi, e, huniq q hq (by rw [← hj'def]; exact hj2)]
    rw [this, cent_card_conj (H := Sg) (mem_inf.2 ⟨(mem_Tg _).2 ⟨_, ht, rfl⟩, xT_mem_Kv ht htV⟩)]
  have h16 : Nat.card C ≤ 16 := hle.trans (hxx ▸ hxc16)
  rcases h48 with h | h
  · exact h
  · rw [hK, h] at h16
    omega

theorem ks8Check_true : ks8Check () = true := ks8Check_of card_two

@[expose] def Ord8 (k : Nat) : Set (Equiv.Perm (Fin 820)) :=
  {x | x * (tP k)⁻¹ ∈ P ∧ orderOf x = 8}

theorem cover {k : Nat} (hk : k < 8) (hV : VK k) {x : Equiv.Perm (Fin 820)} (hx : x ∈ Ord8 k) :
    ∃ j < 8, ks8Coset[j]! = k ∧ x ∈ conjClass Kv (rK j) := by
  obtain ⟨hxP, h8⟩ := hx
  have hxK := mem_Kv_of hk hV hxP
  have hZ : zpowers x ≤ R := (zpowers_le).2 (Kv_le_R hxK)
  obtain ⟨p, hpP, hpT⟩ := conj_two_group_P hZ (n := 3) (by rw [Nat.card_zpowers, h8]; rfl)
  have hz := hpT x (mem_zpowers x)
  obtain ⟨i, hi, hzi⟩ := (mem_Tg _).1 hz
  have hzc : p⁻¹ * x * p * (tP k)⁻¹ ∈ P := by
    have := conj_coset hk hV hxP (inv_mem (P_le_Kv hpP))
    rwa [inv_inv] at this
  have hLB : LB i = k := coset_unique (lab_spec i hi).1 hk (lab_spec i hi).2 (by rw [hzi]; exact hzc)
  have hx4 : xT i ^ 4 ≠ 1 := by
    have hcp : (p⁻¹ * x * p) ^ 4 = p⁻¹ * x ^ 4 * p := by
      have := conj_pow (a := p⁻¹) (b := x) (i := 4)
      simpa using this
    rw [hzi, hcp]
    intro e
    have : x ^ 4 = 1 := by
      have := congrArg (fun y => p * y * p⁻¹) e
      simpa [mul_assoc] using this
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [h8] at hd
    exact absurd hd (by decide)
  obtain ⟨q, hq, hqi⟩ := listed hi (by rw [hLB]; exact inV_of_VK hV) hx4
  obtain ⟨hj', u, hu, hxu⟩ := listed_conj hq
  have e : x = (p * u) * rK (CJP (SCL q)) * (p * u)⁻¹ := by
    have : p⁻¹ * x * p = u * rK (CJP (SCL q)) * u⁻¹ := by rw [← hxu, hqi, hzi]
    calc x = p * (p⁻¹ * x * p) * p⁻¹ := by group
      _ = _ := by rw [this]; group
  refine ⟨_, hj', ?_, p * u, mul_mem (P_le_Kv hpP) hu, e⟩
  have hm : rK (CJP (SCL q)) = (p * u)⁻¹ * x * (p * u)⁻¹⁻¹ := by rw [inv_inv, e]; group
  have h1 := conj_coset hk hV hxP (inv_mem (mul_mem (P_le_Kv hpP) hu))
  rw [← hm] at h1
  exact coset_unique (coset_lt _ hj') hk (rK_spec hj').2.1 h1

theorem class_sub {j : Nat} (hj : j < 8) : conjClass Kv (rK j) ⊆ Ord8 ks8Coset[j]! := by
  rintro _ ⟨u, hu, rfl⟩
  have hk := coset_lt j hj
  have hV : VK ks8Coset[j]! := by unfold VK; interval_cases j <;> decide
  refine ⟨conj_coset hk hV (rK_spec hj).2.1 hu, ?_⟩
  have h1 : u * rK j * u⁻¹ = (MulAut.conj u) (rK j) := rfl
  rw [h1, MulEquiv.orderOf_eq]
  exact orderOf_rK hj

theorem ncard_class {j N : Nat} (hj : j < 8) (hN : N * centKs ks8Reps[j]! = 4 * 3265920) :
    (conjClass Kv (rK j)).ncard = N := by
  have h := ncard_conjClass_mul_card Kv (rK j)
  rw [card_centKv hj, card_Kv] at h
  have hc : 0 < centKs ks8Reps[j]! := by
    rw [centKs_eq hj]
    exact Nat.mul_pos (by norm_num) Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hc (h.trans hN.symm)

theorem centKs_val {j : Nat} (hj : j < 8) : centKs ks8Reps[j]! = ks8Cent[j]! := by
  have h := ks8Check_true
  simp only [ks8Check, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact (h j hj).2

theorem ncard_Ord8_one {k j N : Nat} (hk : k < 8) (hV : VK k) (hj : j < 8) (hjk : ks8Coset[j]! = k)
    (honly : ∀ j' < 8, ks8Coset[j']! = k → j' = j) (hN : N * ks8Cent[j]! = 4 * 3265920) :
    (Ord8 k).ncard = N := by
  rw [← ncard_class (N := N) hj (by rw [centKs_val hj]; exact hN)]
  congr 1
  refine Set.Subset.antisymm (fun x hx => ?_) (hjk ▸ class_sub hj)
  obtain ⟨j', hj', hjk', hx'⟩ := cover hk hV hx
  rw [← honly j' hj' hjk']
  exact hx'

theorem ncard_Ord8_three {k a b c Na Nb Nc : Nat} (hk : k < 8) (hV : VK k) (ha : a < 8) (hb : b < 8)
    (hc : c < 8) (hak : ks8Coset[a]! = k) (hbk : ks8Coset[b]! = k) (hck : ks8Coset[c]! = k)
    (honly : ∀ j' < 8, ks8Coset[j']! = k → j' = a ∨ j' = b ∨ j' = c)
    (hNa : Na * ks8Cent[a]! = 4 * 3265920) (hNb : Nb * ks8Cent[b]! = 4 * 3265920)
    (hNc : Nc * ks8Cent[c]! = 4 * 3265920) (hab : Na ≠ Nb) (hac : Na ≠ Nc) (hbc : Nb ≠ Nc) :
    (Ord8 k).ncard = Na + Nb + Nc := by
  have ea := ncard_class ha (by rw [centKs_val ha]; exact hNa)
  have eb := ncard_class hb (by rw [centKs_val hb]; exact hNb)
  have ec := ncard_class hc (by rw [centKs_val hc]; exact hNc)
  have hfin : ∀ j, (conjClass Kv (rK j)).Finite := fun j => conjClass_finite Kv (rK j)
  have e : Ord8 k = conjClass Kv (rK a) ∪ conjClass Kv (rK b) ∪ conjClass Kv (rK c) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset (Set.union_subset
      (hak ▸ class_sub ha) (hbk ▸ class_sub hb)) (hck ▸ class_sub hc))
    obtain ⟨j', hj', hjk', hx'⟩ := cover hk hV hx
    rcases honly j' hj' hjk' with rfl | rfl | rfl
    · exact Or.inl (Or.inl hx')
    · exact Or.inl (Or.inr hx')
    · exact Or.inr hx'
  have dab := disjoint_of_ncard (H := Kv) (a := rK a) (b := rK b) (by rw [ea, eb]; exact hab)
  have dac := disjoint_of_ncard (H := Kv) (a := rK a) (b := rK c) (by rw [ea, ec]; exact hac)
  have dbc := disjoint_of_ncard (H := Kv) (a := rK b) (b := rK c) (by rw [eb, ec]; exact hbc)
  rw [e, Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨dac, dbc⟩) ((hfin a).union (hfin b)) (hfin c),
    Set.ncard_union_eq dab (hfin a) (hfin b), ea, eb, ec]

theorem orderOf_eight_iff (x : Equiv.Perm (Fin 820)) : orderOf x = 8 ↔ x ^ 8 = 1 ∧ x ^ 4 ≠ 1 := by
  constructor
  · intro h
    exact ⟨by rw [← h]; exact pow_orderOf_eq_one x,
      pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h]; norm_num)⟩
  · rintro ⟨h8, h4⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)
    simpa using this

theorem count_Ord8 {k : Nat} (hk : k < 8) (hV : VK k) :
    countW (ord8W baseArr.toList (tArr k)) blocks [] = (Ord8 k).ncard := by
  classical
  have hbl : ∀ b ∈ baseArr.toList, b < 820 := by
    have hQb : Q.base.toList.map Fin.val = baseArr.toList := rfl
    rw [← hQb]
    intro b hb
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
    exact y.2
  rw [← card_eq_countW_P (f := ord8W baseArr.toList (tArr k))
    (Pr := fun g => orderOf (g * tP k) = 8) fun w g hw hg => ?_]
  · rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun g => ⟨(g.1 : Equiv.Perm (Fin 820)) * tP k, by
          rw [mul_inv_cancel_right]; exact g.1.2, g.2⟩
        invFun := fun x => ⟨⟨x.1 * (tP k)⁻¹, x.2.1⟩, by
          change orderOf (x.1 * (tP k)⁻¹ * tP k) = 8
          rw [inv_mul_cancel_right]; exact x.2.2⟩
        left_inv := fun g => by
          apply Subtype.ext
          apply Subtype.ext
          change (g.1 : Equiv.Perm (Fin 820)) * tP k * (tP k)⁻¹ = g.1
          group
        right_inv := fun x => by
          apply Subtype.ext
          change x.1 * (tP k)⁻¹ * tP k = x.1
          group }
  · have hx : g * tP k ∈ Kv := ⟨g, hg, k, hk, hV, rfl⟩
    have hv : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    have hsq : ∀ y ∈ Kv, y * y ∈ P := by
      rintro _ ⟨a, ha, m, hm, hmV, rfl⟩
      have hN := (mem_normalizer_iff.1 (tP_mem_normalizer m) a).1 ha
      have e : a * tP m * (a * tP m) = a * (tP m * a * (tP m)⁻¹) * (tP m * tP m) := by group
      rw [e, tP_mul_eq hm hm, VK_sq m hm hmV, tP_zero, mul_one]
      exact mul_mem ha hN
    have h4 : (g * tP k) ^ 4 ∈ P := by
      have e : (g * tP k) ^ 4 = (g * tP k * (g * tP k)) * (g * tP k * (g * tP k)) := by
        have n4 : (4 : Nat) = 2 * 2 := rfl
        rw [n4, pow_mul, pow_two, pow_two]
      rw [e]
      exact mul_mem (hsq _ hx) (hsq _ hx)
    have h8 : (g * tP k) ^ 8 ∈ P := by
      have n8 : (8 : Nat) = 4 * 2 := rfl
      rw [n8, pow_mul, pow_two]
      exact mul_mem h4 h4
    have key : ∀ e : ℕ, (g * tP k) ^ e ∈ P →
        (fixB baseArr.toList (tArr k :: w) e = true ↔ (g * tP k) ^ e = 1) := by
      intro e he
      rw [fixB_iff hbl hv e]
      constructor
      · exact baseFaithful_P _ he
      · intro h y _
        rw [h]
        rfl
    unfold ord8W
    rw [orderOf_eight_iff]
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      obtain ⟨h8', h4'⟩ := h
      refine ⟨(key 8 h8).1 h8', fun h4'' => ?_⟩
      rw [(key 4 h4).2 h4''] at h4'
      exact absurd h4' (by decide)
    · rintro ⟨h8', h4'⟩
      rw [Bool.and_eq_true]
      refine ⟨(key 8 h8).2 h8', ?_⟩
      cases hb : fixB baseArr.toList (tArr k :: w) 4
      · rfl
      · exact absurd ((key 4 h4).1 hb) h4'

theorem ks8Counts_true : ks8Counts () = true := by
  have c0 : (Ord8 0).ncard = 408240 :=
    ncard_Ord8_one (j := 0) (by norm_num) (Or.inl rfl) (by norm_num) (by decide)
      (fun j' hj' h => by interval_cases j' <;> simp_all [ks8Coset]) (by decide)
  have c2 : (Ord8 2).ncard = 408240 :=
    ncard_Ord8_one (j := 1) (by norm_num) (Or.inr (Or.inl rfl)) (by norm_num) (by decide)
      (fun j' hj' h => by interval_cases j' <;> simp_all [ks8Coset]) (by decide)
  have c5 : (Ord8 5).ncard = 816480 + 204120 + 68040 :=
    ncard_Ord8_three (a := 2) (b := 3) (c := 4) (by norm_num) (Or.inr (Or.inr (Or.inl rfl)))
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      (fun j' hj' h => by interval_cases j' <;> simp_all [ks8Coset]) (by decide) (by decide)
      (by decide) (by norm_num) (by norm_num) (by norm_num)
  have c7 : (Ord8 7).ncard = 816480 + 204120 + 68040 :=
    ncard_Ord8_three (a := 5) (b := 6) (c := 7) (by norm_num) (Or.inr (Or.inr (Or.inr rfl)))
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      (fun j' hj' h => by interval_cases j' <;> simp_all [ks8Coset]) (by decide) (by decide)
      (by decide) (by norm_num) (by norm_num) (by norm_num)
  simp only [ks8Counts, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi
  interval_cases i
  · change countW (ord8W baseArr.toList (tArr 0)) blocks [] = 408240
    rw [count_Ord8 (k := 0) (by norm_num) (Or.inl rfl), c0]
  · change countW (ord8W baseArr.toList (tArr 2)) blocks [] = 408240
    rw [count_Ord8 (k := 2) (by norm_num) (Or.inr (Or.inl rfl)), c2]
  · change countW (ord8W baseArr.toList (tArr 5)) blocks [] = 1088640
    rw [count_Ord8 (k := 5) (by norm_num) (Or.inr (Or.inr (Or.inl rfl))), c5]
  · change countW (ord8W baseArr.toList (tArr 7)) blocks [] = 1088640
    rw [count_Ord8 (k := 7) (by norm_num) (Or.inr (Or.inr (Or.inr rfl))), c7]

end CertificateChecks.KernelKsEight.SylG8

end
