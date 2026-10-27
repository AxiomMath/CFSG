module

public import Certificates.Kernel.Misc.Sp6SR.FactsR
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6SR
open CertificateChecks.KernelMisc.Sp6Transv.Facts (orB_true commF_iff)
open CFSG.KC.LQT.P (letB)
open CFSG.KC.Ord (andB orB)

variable {z : Fin 3 → H6} {s : H6}

theorem comm_of_commF {g h : H6} (e : commF (enc6 g) (enc6 h) = true) : g * h = h * g :=
  eq_of_enc (by rw [emul, emul]; exact Nat.eq_of_beq_eq_true e)

theorem ne_of_not_beq {a b : ℕ} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem commF_of_comm {g h : H6} (e : g * h = h * g) : commF (enc6 g) (enc6 h) = true := by
  unfold commF
  rw [Nat.beq_eq, ← emul, ← emul, e]

theorem pow4 (v : H6) : v ^ 4 = v * v * (v * v) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem card_cen_inf_mul_le {S : Subgroup H6} {x : H6} {n : ℕ} (f : Fin n → H6)
    (hf : ∀ k, f k ∈ S) (hinj : Function.Injective fun k => f k * x * (f k)⁻¹) :
    n * Nat.card (Subgroup.centralizer ({x} : Set H6) ⊓ S : Subgroup H6) ≤ Nat.card S := by
  set Hc := Subgroup.centralizer ({x} : Set H6)
  have hmul := Subgroup.relIndex_mul_card (H := Hc) (K := S)
  have hlen : n ≤ Hc.relIndex S := by
    let φ : Fin n → S ⧸ Hc.subgroupOf S := fun k => QuotientGroup.mk ⟨f k, hf k⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
      have h2 : x * ((f a)⁻¹ * f b) = ((f a)⁻¹ * f b) * x := h1 x (Set.mem_singleton x)
      refine hinj ?_
      change f a * x * (f a)⁻¹ = f b * x * (f b)⁻¹
      calc f a * x * (f a)⁻¹ = f a * (x * ((f a)⁻¹ * f b)) * (f b)⁻¹ := by group
        _ = f a * (((f a)⁻¹ * f b) * x) * (f b)⁻¹ := by rw [h2]
        _ = f b * x * (f b)⁻¹ := by group
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  calc n * Nat.card (Hc ⊓ S : Subgroup H6) ≤ Hc.relIndex S * Nat.card (Hc ⊓ S : Subgroup H6) :=
        Nat.mul_le_mul_right _ hlen
    _ = Nat.card S := hmul

theorem Hyp.eq_cen_of (H : Hyp z s) {L : Subgroup H6} {x : H6} {N n : ℕ}
    (hL : L ≤ Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({x} : Set H6))
    (hc : Nat.card L = N) (hn : n * N = 4608) (hpos : 0 < n) {E P S : ℕ → ℕ}
    (ht : ∀ k < n, treeAt cstep (enc6 x) (fun l => l) 2 E P k = true)
    (hs : ∀ i < n, sortAt n E S i = true) :
    L = Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({x} : Set H6) := by
  have hc' := conj_tree_mem (g := fun l => KY (Nat.add 13 l)) (gi := fun l => KY (Nat.add 15 l))
    (fun l hl => (enc_cgl l hl).1) (fun l hl => (enc_cgl l hl).2) (fun l _ => H.cgl_mem l) ht
  choose! h hh eh using hc'
  have hd := sort_distinct_proved hs
  have hle := card_cen_inf_mul_le (S := Subgroup.centralizer ({s} : Set H6)) (x := x)
    (fun k : Fin n => h k) (fun k => hh k k.2) (by
      intro a b e
      exact Fin.ext (hd a a.2 b b.2 (by rw [eh a a.2, eh b b.2]; exact congrArg enc6 e)))
  rw [H.card_cen, inf_comm] at hle
  refine Subgroup.eq_of_le_of_card_ge hL ?_
  rw [hc]
  by_contra! hlt
  have : n * N < n * Nat.card ↥(Subgroup.centralizer ({s} : Set H6) ⊓
      Subgroup.centralizer ({x} : Set H6)) := Nat.mul_lt_mul_of_pos_left hlt hpos
  linarith

theorem Hyp.pair_mem (H : Hyp z s) {r : ℕ} (hr : r < 4608) :
    ∃ g ∈ Subgroup.centralizer ({s} : Set H6), enc6 g = pairE TE EZ r := by
  obtain ⟨a, ha, ea⟩ := T_facts.1 (r % 512) (Nat.mod_lt _ (by norm_num))
  obtain ⟨b, hb, eb⟩ := H.E9_facts.1 (r / 512) (by omega)
  exact ⟨a * b, mul_mem (H.T_le ha) (H.E9_le hb), by rw [emul, ea, eb]; rfl⟩

theorem k_parts :
    (∀ l < 2, KG l < 4608 ∧ commF (pairE TE EZ (KG l)) (KY 1) = true) ∧
    (∀ k < 144, treeAt MULF ONE (fun l => pairE TE EZ (KG l)) 2 KE KP k = true) ∧
    (∀ i < 144, sortAt 144 KE KS i = true) ∧
    (∀ k < 144, closedAt MULF (fun l => pairE TE EZ (KG l)) 2 144 KE KC k = true) ∧
    (∀ k < 144, KI k < 144 ∧ MULF (KE k) (KE (KI k)) = ONE) ∧
    (∀ k < 32, treeAt cstep (KY 1) (fun l => l) 2 ZE ZP k = true) ∧
    (∀ i < 32, sortAt 32 ZE ZS i = true) := by
  have h : kB 0 = true := chK.all 0 (by norm_num)
  unfold kB at h
  rw [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h7⟩ := andB_eq_true h
  refine ⟨fun l hl => ?_, rall h2, rall h3, rall h4, fun k hk => ?_, rall h6, rall h7⟩
  · obtain ⟨e1, e2⟩ := andB_eq_true ((allN_iff _ _).1 h1 l hl)
    exact ⟨Nat.blt_eq.mp e1, e2⟩
  · obtain ⟨e1, e2⟩ := andB_eq_true ((allN_iff _ _).1 h5 k hk)
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩

@[expose] noncomputable def kgens : List H6 :=
  (List.range 2).map fun l => eltOf (pairE TE EZ (KG l))

@[expose] noncomputable def KSub : Subgroup H6 := Subgroup.closure {g | g ∈ kgens}

theorem Hyp.kgens_mem (H : Hyp z s) :
    ∀ l < 2, eltOf (pairE TE EZ (KG l)) ∈ Subgroup.centralizer ({s} : Set H6) ∧
      enc6 (eltOf (pairE TE EZ (KG l))) = pairE TE EZ (KG l) := by
  intro l hl
  obtain ⟨g, hg, eg⟩ := H.pair_mem (k_parts.1 l hl).1
  rw [eltOf_eq eg]
  exact ⟨hg, eg⟩

theorem Hyp.K_facts (H : Hyp z s) :
    (∀ k < 144, ∃ g ∈ KSub, enc6 g = KE k) ∧ Nat.card KSub = 144 ∧
      ∀ g ∈ KSub, ∃ k < 144, enc6 g = KE k := by
  have hG : ∀ j < kgens.length, pairE TE EZ (KG j) = enc6 (kgens.getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa [kgens] using hj
    have e : kgens.getD j 1 = eltOf (pairE TE EZ (KG j)) := getD_map_range _ hj'
    rw [e, (H.kgens_mem j hj').2]
  obtain ⟨-, h2, h3, h4, -⟩ := k_parts
  obtain ⟨e1, -, e3⟩ := clos_card_proved enc6_enc kgens hG (by norm_num) h2 h3
  obtain ⟨e4, e5⟩ := e3 h4
  exact ⟨e1, e4, e5⟩

theorem Hyp.K_le (H : Hyp z s) :
    KSub ≤ Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({z 0} : Set H6) := by
  rw [KSub, Subgroup.closure_le]
  intro g hg
  simp only [kgens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  obtain ⟨m1, m2⟩ := H.kgens_mem l hl
  rw [SetLike.mem_coe]
  refine ⟨m1, ?_⟩
  change _ ∈ Subgroup.centralizer ({z 0} : Set H6)
  rw [← commF_iff, m2, H.ez0]
  exact (k_parts.1 l hl).2

theorem Hyp.K_eq (H : Hyp z s) :
    KSub = Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({z 0} : Set H6) := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := k_parts
  rw [← H.ez0] at h6
  exact H.eq_cen_of H.K_le H.K_facts.2.1 (n := 32) (by norm_num) (by norm_num) h6 h7

theorem Hyp.K_inv (H : Hyp z s) {g : H6} (hg : g ∈ KSub) {k : ℕ} (hk : k < 144)
    (eg : enc6 g = KE k) : enc6 g⁻¹ = KE (KI k) := by
  obtain ⟨-, -, -, -, h5, -⟩ := k_parts
  obtain ⟨i1, i2⟩ := h5 k hk
  obtain ⟨g', -, eg'⟩ := H.K_facts.1 _ i1
  rw [← inv_of_mul eg eg' i2]
  exact eg'

theorem conjF_of {g x : H6} {a b c : ℕ} (ha : enc6 g = a) (hb : enc6 g⁻¹ = b) (hc : enc6 x = c) :
    conjF a b c = enc6 (g * x * g⁻¹) := by
  rw [← ha, ← hb, ← hc, conjF, emul, emul]

theorem y_parts :
    (∀ l < 2, YG l < 4608 ∧ commF (pairE TE EZ (YG l)) (KY 6) = true) ∧
    (∀ k < 72, treeAt MULF ONE (fun l => pairE TE EZ (YG l)) 2 YE YP k = true) ∧
    (∀ i < 72, sortAt 72 YE YS i = true) ∧
    (∀ k < 72, closedAt MULF (fun l => pairE TE EZ (YG l)) 2 72 YE YC k = true) ∧
    (∀ k < 64, treeAt cstep (KY 6) (fun l => l) 2 XE XP k = true) ∧
    (∀ i < 64, sortAt 64 XE XS i = true) := by
  have h : yB 0 = true := chY.all 0 (by norm_num)
  unfold yB at h
  rw [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h6, h7⟩ := andB_eq_true h
  refine ⟨fun l hl => ?_, rall h2, rall h3, rall h4, rall h6, rall h7⟩
  obtain ⟨e1, e2⟩ := andB_eq_true ((allN_iff _ _).1 h1 l hl)
  exact ⟨Nat.blt_eq.mp e1, e2⟩

@[expose] noncomputable def ygens : List H6 :=
  (List.range 2).map fun l => eltOf (pairE TE EZ (YG l))

@[expose] noncomputable def YSub : Subgroup H6 := Subgroup.closure {g | g ∈ ygens}

theorem Hyp.ygens_mem (H : Hyp z s) :
    ∀ l < 2, eltOf (pairE TE EZ (YG l)) ∈ Subgroup.centralizer ({s} : Set H6) ∧
      enc6 (eltOf (pairE TE EZ (YG l))) = pairE TE EZ (YG l) := by
  intro l hl
  obtain ⟨g, hg, eg⟩ := H.pair_mem (y_parts.1 l hl).1
  rw [eltOf_eq eg]
  exact ⟨hg, eg⟩

theorem Hyp.Y_facts (H : Hyp z s) :
    (∀ k < 72, ∃ g ∈ YSub, enc6 g = YE k) ∧ Nat.card YSub = 72 ∧
      ∀ g ∈ YSub, ∃ k < 72, enc6 g = YE k := by
  have hG : ∀ j < ygens.length, pairE TE EZ (YG j) = enc6 (ygens.getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa [ygens] using hj
    have e : ygens.getD j 1 = eltOf (pairE TE EZ (YG j)) := getD_map_range _ hj'
    rw [e, (H.ygens_mem j hj').2]
  obtain ⟨-, h2, h3, h4, -⟩ := y_parts
  obtain ⟨e1, -, e3⟩ := clos_card_proved enc6_enc ygens hG (by norm_num) h2 h3
  obtain ⟨e4, e5⟩ := e3 h4
  exact ⟨e1, e4, e5⟩

theorem Hyp.Y_le (H : Hyp z s) :
    YSub ≤ Subgroup.centralizer ({s} : Set H6) ⊓
      Subgroup.centralizer ({z 0 * (z 1 * z 2)} : Set H6) := by
  rw [YSub, Subgroup.closure_le]
  intro g hg
  simp only [ygens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  obtain ⟨m1, m2⟩ := H.ygens_mem l hl
  rw [SetLike.mem_coe]
  refine ⟨m1, ?_⟩
  change _ ∈ Subgroup.centralizer ({z 0 * (z 1 * z 2)} : Set H6)
  rw [← commF_iff, m2, H.ex2]
  exact (y_parts.1 l hl).2

theorem Hyp.Y_eq (H : Hyp z s) :
    YSub = Subgroup.centralizer ({s} : Set H6) ⊓
      Subgroup.centralizer ({z 0 * (z 1 * z 2)} : Set H6) := by
  obtain ⟨-, -, -, -, h6, h7⟩ := y_parts
  rw [← H.ex2] at h6
  exact H.eq_cen_of H.Y_le H.Y_facts.2.1 (n := 64) (by norm_num) (by norm_num) h6 h7

theorem w_parts : WI 0 < 72 ∧ MULF (MULF (YE (WI 0)) (YE (WI 0))) (MULF (YE (WI 0)) (YE (WI 0))) =
      ONE ∧ YE (WI 0) ≠ ONE ∧ YE (WI 0) ≠ KY 0 ∧ WI 1 < 144 ∧
    MULF (KE (WI 1)) (KE (WI 1)) = ONE ∧ KE (WI 1) ≠ ONE ∧ KE (WI 1) ≠ KY 0 ∧
    ∀ k < 144, commF (conjF (KE k) (KE (KI k)) (KE (WI 1))) (KE (WI 1)) = true := by
  have h : wB 0 = true := chW.all 0 (by norm_num)
  unfold wB at h
  simp only [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h⟩ := andB_eq_true h
  obtain ⟨h7, h⟩ := andB_eq_true h
  obtain ⟨h8, h9⟩ := andB_eq_true h
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, ne_of_not_beq h3, ne_of_not_beq h4,
    Nat.blt_eq.mp h5, Nat.eq_of_beq_eq_true h6, ne_of_not_beq h7, ne_of_not_beq h8,
    (allN_iff _ _).1 h9⟩

theorem Hyp.clause_i (H : Hyp z s) :
    ∃ v ∈ Subgroup.centralizer ({s} : Set H6) ⊓
      Subgroup.centralizer ({z 0 * (z 1 * z 2)} : Set H6), v ^ 4 = 1 ∧ v ≠ 1 ∧ v ≠ s := by
  obtain ⟨w1, w2, w3, w4, -⟩ := w_parts
  obtain ⟨v, hv, ev⟩ := H.Y_facts.1 _ w1
  refine ⟨v, H.Y_le hv, eq_of_enc ?_, ne_of_enc ev enc_one w3, ne_of_enc ev H.es w4⟩
  rw [pow4, emul, emul, ev, enc_one, w2]

theorem Hyp.clause_ii (H : Hyp z s) :
    ∃ v ∈ Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({z 0} : Set H6),
      v * v = 1 ∧ (∀ g ∈ Subgroup.centralizer ({s} : Set H6) ⊓
        Subgroup.centralizer ({z 0} : Set H6), g * v * g⁻¹ * v = v * (g * v * g⁻¹)) ∧
      v ≠ 1 ∧ v ≠ s := by
  obtain ⟨-, -, -, -, w5, w6, w7, w8, w9⟩ := w_parts
  obtain ⟨v, hv, ev⟩ := H.K_facts.1 _ w5
  refine ⟨v, H.K_le hv, eq_of_enc (by rw [emul, ev, enc_one, w6]), fun g hg => ?_,
    ne_of_enc ev enc_one w7, ne_of_enc ev H.es w8⟩
  rw [← H.K_eq] at hg
  obtain ⟨k, hk, ek⟩ := H.K_facts.2.2 g hg
  have h := w9 k hk
  rw [conjF_of ek (H.K_inv hg hk ek) ev, ← ev] at h
  exact comm_of_commF h

theorem Hyp.mem_cenS_of (H : Hyp z s) {t : ℕ} (ht : t < 3) {v : H6}
    (h : ∀ l < NG t, commF (enc6 v) (rgen t l) = true) :
    v ∈ Subgroup.centralizer (RSub t : Set H6) := by
  have hle : RSub t ≤ Subgroup.centralizer ({v} : Set H6) := by
    rw [RSub, Subgroup.closure_le]
    intro g hg
    simp only [rgens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    rw [SetLike.mem_coe, ← commF_iff]
    have e : commF (enc6 v) (enc6 (eltOf (rgen t l))) = true := by
      rw [enc_eltOf (H.rgen_ex t ht l hl)]
      exact h l hl
    exact commF_of_comm (comm_of_commF e).symm
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hr)

theorem Hyp.clause_8 (H : Hyp z s) :
    ∀ v ∈ Subgroup.centralizer ({s} : Set H6) ⊓
      Subgroup.centralizer ({z 0 * (z 1 * z 2)} : Set H6), v ^ 4 = 1 →
        v ∈ Subgroup.centralizer (RSub 0 : Set H6) := by
  intro v hv h4
  rw [← H.Y_eq] at hv
  obtain ⟨i, hi, ei⟩ := H.Y_facts.2.2 v hv
  have h := (allN_iff _ _).1 (ch8.all 0 (by norm_num)) i hi
  simp only [letB_eq] at h
  have hp : Nat.beq (MULF (MULF (YE i) (YE i)) (MULF (YE i) (YE i))) ONE = true := by
    rw [Nat.beq_eq, ← ei, ← emul, ← emul, ← pow4, h4, enc_one]
  rw [hp] at h
  rcases orB_true h with h | h
  · exact absurd h (by decide)
  refine H.mem_cenS_of (by norm_num) fun l hl => ?_
  rw [ei]
  exact (allN_iff _ _).1 h l hl

theorem Hyp.clause_32 (H : Hyp z s) :
    ∀ v ∈ Subgroup.centralizer ({s} : Set H6) ⊓ Subgroup.centralizer ({z 0} : Set H6),
      v * v = 1 → (∀ g ∈ Subgroup.centralizer ({s} : Set H6) ⊓
        Subgroup.centralizer ({z 0} : Set H6), g * v * g⁻¹ * v = v * (g * v * g⁻¹)) →
          v ∈ Subgroup.centralizer (RSub 1 : Set H6) := by
  intro v hv hsq hcomm
  rw [← H.K_eq] at hv hcomm
  obtain ⟨k, hk, ek⟩ := H.K_facts.2.2 v hv
  have h := (allN_iff _ _).1 (ch32.all 0 (by norm_num)) k hk
  simp only [letB_eq] at h
  have hp : Nat.beq (MULF (KE k) (KE k)) ONE = true := by
    rw [Nat.beq_eq, ← ek, ← emul, hsq, enc_one]
  rw [hp] at h
  rcases orB_true h with h | h
  · exact absurd h (by decide)
  rcases orB_true h with h | h
  · refine H.mem_cenS_of (by norm_num) fun l hl => ?_
    rw [ek]
    exact (allN_iff _ _).1 h l hl
  · obtain ⟨h1, h2⟩ := andB_eq_true h
    obtain ⟨g, hg, eg⟩ := H.K_facts.1 _ (Nat.blt_eq.mp h1)
    rw [conjF_of eg (H.K_inv hg (Nat.blt_eq.mp h1) eg) ek, ← ek] at h2
    rw [commF_of_comm (hcomm g hg)] at h2
    exact absurd h2 (by decide)

theorem Hyp.card_cnt (H : Hyp z s) {t : ℕ} (ht : t < 3) {y : H6} {x : ℕ} (ey : enc6 y = x) :
    Nat.card ↥(RSub t ⊓ Subgroup.centralizer ({y} : Set H6)) = cntT t x := by
  obtain ⟨r1, -, r3, r4⟩ := H.R_facts t ht
  exact card_inf_of_cnt r1 r3 r4 fun k _ g hg => by
    beta_reduce
    rw [← hg, ← ey]
    exact commF_iff g y

theorem cnt_parts : cntT 0 (KY 1) = 8 ∧ cntT 0 (KY 6) = 2 ∧ cntT 0 (KY 4) = 2 ∧
    cntT 1 (KY 1) = 2 ∧ cntT 1 (KY 6) = 8 ∧ cntT 1 (KY 4) = 2 ∧
    cntT 2 (KY 1) = 8 ∧ cntT 2 (KY 6) = 8 ∧ cntT 2 (KY 4) = 2 := by
  have h : cntB 0 = true := chCnt.all 0 (by norm_num)
  unfold cntB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h⟩ := andB_eq_true h
  obtain ⟨h7, h⟩ := andB_eq_true h
  obtain ⟨h8, h9⟩ := andB_eq_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9⟩

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
