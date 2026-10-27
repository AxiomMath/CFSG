module

public import CFSG.Certificates.Kernel.S5Ext.Group

public section

open CFSG.CGT.PushingUpLit.SolK CFSG.Certificates.Kernel.S5K

namespace CertificateChecks.S5K

structure S5KFacts where
  N : ℕ
  tab : ℕ → Fin 32 → Fin 32
  tab_hom : ∀ e < N, ∀ i j, tab e (extraMulFin i j) = extraMulFin (tab e i) (tab e j)
  tab_injective : ∀ e < N, Function.Injective (tab e)
  complete : ∀ f : Fin 32 → Fin 32, (∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j)) →
    Function.Injective f → ∃ e, e < N ∧ tab e = f
  tab_inj : ∀ e e', e < N → e' < N → tab e = tab e' → e = e'
  N_eq : N = 2 ^ 7 * 9
  M : ℕ
  ltab : ℕ → Fin 32 → Fin 32
  ltab_hom : ∀ g < M, ∀ i j, ltab g (extraMulFin i j) = extraMulFin (ltab g i) (ltab g j)
  ltab_injective : ∀ g < M, Function.Injective (ltab g)
  ltab_inj : ∀ g g', g < M → g' < M → ltab g = ltab g' → g = g'
  M_eq : M = 2 ^ 7
  lmul : ℕ → ℕ → ℕ
  lmul_lt : ∀ g c, g < M → c < M → lmul g c < M
  lmul_tab : ∀ g c, g < M → c < M → ∀ x, ltab (lmul g c) x = ltab g (ltab c x)
  lide : ℕ
  lide_lt : lide < M
  lide_tab : ∀ x, ltab lide x = x
  linv : ℕ → ℕ
  linv_lt : ∀ g, g < M → linv g < M
  linv_tab : ∀ g, g < M → ∀ x, ltab (linv g) (ltab g x) = x
  lci : Fin 32 → ℕ
  lci_lt : ∀ i, lci i < M
  lci_tab : ∀ i, IsConjP i (ltab (lci i))
  K : ℕ
  Cat : ℕ → ℕ → Prop
  cat_lt : ∀ k < K, ∀ g, Cat k g → g < M
  cat_one : ∃ k < K, ∀ g, Cat k g ↔ g = lide
  cat_step : ∀ k < K, ∀ g < M, ¬ Cat k g → Cat k (lmul g g) →
    (∀ c, Cat k c → Cat k (lmul (lmul g c) (linv g))) →
    ∃ k' < K, ∃ h < M, Cat k' g ∧ ∀ x, Cat k' x ↔ Cat k x ∨ ∃ c, Cat k c ∧ x = lmul h c
  cat_wit : ∀ k < K, ∃ (as : List ℕ) (ts : List (Fin 32)),
    as.length + ts.length ≤ 4 ∧ (∀ a ∈ as, Cat k a) ∧ (∀ t ∈ ts, Cat k (lci t)) ∧
    (∀ P : ℕ → Prop, (∀ i, Cat k (lci i) → P (lci i)) →
      (∀ a ∈ as, ∀ x, x < M → P x → P (lmul a x)) → ∀ α, Cat k α → P α) ∧
    (∀ Q : Fin 32 → Prop, (∀ α, Cat k α → ∀ t ∈ ts, Q (ltab α t)) →
      (∀ x y, Q x → Q y → Q (extraMulFin x y)) → ∀ i, Cat k (lci i) → Q i)

namespace S5KFacts

variable (F : S5KFacts)

noncomputable def gperm (e : ℕ) : Equiv.Perm (Fin 32) :=
  if h : e < F.N then Equiv.ofBijective (F.tab e)
    (Finite.injective_iff_bijective.1 (F.tab_injective e h)) else 1

noncomputable def lperm (g : ℕ) : Equiv.Perm (Fin 32) :=
  if h : g < F.M then Equiv.ofBijective (F.ltab g)
    (Finite.injective_iff_bijective.1 (F.ltab_injective g h)) else 1

theorem gperm_apply {e : ℕ} (he : e < F.N) (x : Fin 32) : F.gperm e x = F.tab e x := by
  simp [gperm, he]

theorem lperm_apply {g : ℕ} (hg : g < F.M) (x : Fin 32) : F.lperm g x = F.ltab g x := by
  simp [lperm, hg]

theorem gperm_mem {e : ℕ} (he : e < F.N) : F.gperm e ∈ autP0 := mem_autP0.2 fun i j => by
  simp only [F.gperm_apply he]
  exact F.tab_hom e he i j

theorem lperm_mem {g : ℕ} (hg : g < F.M) : F.lperm g ∈ autP0 := mem_autP0.2 fun i j => by
  simp only [F.lperm_apply hg]
  exact F.ltab_hom g hg i j

theorem gperm_inj {e e' : ℕ} (he : e < F.N) (he' : e' < F.N) (h : F.gperm e = F.gperm e') :
    e = e' :=
  F.tab_inj e e' he he' (funext fun x => by rw [← F.gperm_apply he, ← F.gperm_apply he', h])

theorem lperm_inj {g g' : ℕ} (hg : g < F.M) (hg' : g' < F.M) (h : F.lperm g = F.lperm g') :
    g = g' :=
  F.ltab_inj g g' hg hg' (funext fun x => by rw [← F.lperm_apply hg, ← F.lperm_apply hg', h])

theorem lperm_mul {g c : ℕ} (hg : g < F.M) (hc : c < F.M) :
    F.lperm (F.lmul g c) = F.lperm g * F.lperm c :=
  Equiv.ext fun x => by
    rw [F.lperm_apply (F.lmul_lt g c hg hc), Equiv.Perm.coe_mul, Function.comp_apply,
      F.lperm_apply hg, F.lperm_apply hc, F.lmul_tab g c hg hc]

theorem lperm_ide : F.lperm F.lide = 1 :=
  Equiv.ext fun x => by rw [F.lperm_apply F.lide_lt, F.lide_tab, Equiv.Perm.coe_one, id]

theorem lperm_inv {g : ℕ} (hg : g < F.M) : F.lperm (F.linv g) = (F.lperm g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  exact Equiv.ext fun x => by
    rw [Equiv.Perm.coe_mul, Function.comp_apply, F.lperm_apply (F.linv_lt g hg),
      F.lperm_apply hg, F.linv_tab g hg, Equiv.Perm.coe_one, id]

noncomputable def idx (σ : Equiv.Perm (Fin 32)) : ℕ :=
  Classical.epsilon fun e => e < F.N ∧ F.gperm e = σ

theorem idx_spec {σ : Equiv.Perm (Fin 32)} (hσ : σ ∈ autP0) :
    F.idx σ < F.N ∧ F.gperm (F.idx σ) = σ := by
  apply Classical.epsilon_spec (p := fun e => e < F.N ∧ F.gperm e = σ)
  obtain ⟨e, he, hfe⟩ := F.complete σ (mem_autP0.1 hσ) σ.injective
  exact ⟨e, he, Equiv.ext fun x => by rw [F.gperm_apply he, hfe]⟩

theorem idx_lt {σ : Equiv.Perm (Fin 32)} (hσ : σ ∈ autP0) : F.idx σ < F.N := (F.idx_spec hσ).1

theorem gperm_idx {σ : Equiv.Perm (Fin 32)} (hσ : σ ∈ autP0) : F.gperm (F.idx σ) = σ :=
  (F.idx_spec hσ).2

theorem idx_gperm {e : ℕ} (he : e < F.N) : F.idx (F.gperm e) = e :=
  F.gperm_inj (F.idx_lt (F.gperm_mem he)) he (F.gperm_idx (F.gperm_mem he))

def S0 : Subgroup (Equiv.Perm (Fin 32)) where
  carrier := {σ | ∃ g < F.M, F.lperm g = σ}
  one_mem' := ⟨F.lide, F.lide_lt, F.lperm_ide⟩
  mul_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨F.lmul g c, F.lmul_lt g c hg hc, F.lperm_mul hg hc⟩
  inv_mem' := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨F.linv g, F.linv_lt g hg, F.lperm_inv hg⟩

theorem S0_le : F.S0 ≤ autP0 := by
  rintro _ ⟨g, hg, rfl⟩
  exact F.lperm_mem hg

theorem card_S0 : Nat.card F.S0 = 2 ^ 7 := by
  let f : Fin F.M → F.S0 := fun g => ⟨F.lperm g, g, g.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g g' h => Fin.ext (F.lperm_inj g.2 g'.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin, F.M_eq]

def catSet (k : ℕ) : Set (Equiv.Perm (Fin 32)) := {σ | ∃ g, F.Cat k g ∧ F.lperm g = σ}

theorem cat_complete' (R : Subgroup (Equiv.Perm (Fin 32))) (hR : R ≤ F.S0) :
    ∃ k < F.K, (R : Set (Equiv.Perm (Fin 32))) = F.catSet k := by
  have hS0 : IsPGroup 2 F.S0 := IsPGroup.of_card F.card_S0
  refine cat_complete F.S0 hS0 F.K F.catSet ?_ ?_ R hR
  · obtain ⟨k, hk, hk1⟩ := F.cat_one
    refine ⟨k, hk, Set.ext fun σ => ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, rfl⟩
      rw [(hk1 g).1 hg, F.lperm_ide]
      rfl
    · rintro rfl
      exact ⟨F.lide, (hk1 _).2 rfl, F.lperm_ide⟩
  · intro k hk B hB g hg hgB hgg hgN
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    have hmemB : ∀ c, F.Cat k c → F.lperm c ∈ B := fun c hc => by
      rw [← SetLike.mem_coe, hB]
      exact ⟨c, hc, rfl⟩
    have hBmem : ∀ c, c < F.M → F.lperm c ∈ B → F.Cat k c := fun c hc hcB => by
      rw [← SetLike.mem_coe, hB] at hcB
      obtain ⟨c', hc', hcc'⟩ := hcB
      rwa [← F.lperm_inj (F.cat_lt k hk c' hc') hc hcc']
    have h1 : ¬ F.Cat k g₀ := fun h => hgB (hmemB g₀ h)
    have h2 : F.Cat k (F.lmul g₀ g₀) :=
      hBmem _ (F.lmul_lt _ _ hg₀ hg₀) (by rwa [F.lperm_mul hg₀ hg₀])
    have h3 : ∀ c, F.Cat k c → F.Cat k (F.lmul (F.lmul g₀ c) (F.linv g₀)) := fun c hc => by
      have hc' := F.cat_lt k hk c hc
      refine hBmem _ (F.lmul_lt _ _ (F.lmul_lt _ _ hg₀ hc') (F.linv_lt _ hg₀)) ?_
      rw [F.lperm_mul (F.lmul_lt _ _ hg₀ hc') (F.linv_lt _ hg₀), F.lperm_mul hg₀ hc',
        F.lperm_inv hg₀]
      exact hgN _ (hmemB c hc)
    obtain ⟨k', hk', h, hh, hk'g, hk'x⟩ := F.cat_step k hk g₀ hg₀ h1 h2 h3
    obtain ⟨c₀, hc₀, hgc₀⟩ := ((hk'x g₀).1 hk'g).resolve_left h1
    have hc₀' := F.cat_lt k hk c₀ hc₀
    have hgh : F.lperm g₀ = F.lperm h * F.lperm c₀ := by rw [hgc₀, F.lperm_mul hh hc₀']
    refine ⟨k', hk', fun σ => ⟨?_, ?_⟩⟩
    · rintro ⟨x, hx, rfl⟩
      rcases (hk'x x).1 hx with hx | ⟨c, hc, rfl⟩
      · exact Or.inl (hmemB x hx)
      · refine Or.inr ⟨(F.lperm c₀)⁻¹ * F.lperm c,
          B.mul_mem (B.inv_mem (hmemB c₀ hc₀)) (hmemB c hc), ?_⟩
        rw [F.lperm_mul hh (F.cat_lt k hk c hc), hgh]
        group
    · rintro (hσ | ⟨b, hb, rfl⟩)
      · have hσS : σ ∈ F.S0 := by
          rw [← SetLike.mem_coe, hB] at hσ
          obtain ⟨c, hc, rfl⟩ := hσ
          exact ⟨c, F.cat_lt k hk c hc, rfl⟩
        obtain ⟨c, hc, rfl⟩ := hσS
        exact ⟨c, (hk'x c).2 (Or.inl (hBmem c hc hσ)), rfl⟩
      · have hbS : b ∈ F.S0 := by
          rw [← SetLike.mem_coe, hB] at hb
          obtain ⟨c, hc, rfl⟩ := hb
          exact ⟨c, F.cat_lt k hk c hc, rfl⟩
        obtain ⟨c, hc, rfl⟩ := hbS
        have hcB := hBmem c hc hb
        have hc0c : F.Cat k (F.lmul c₀ c) :=
          hBmem _ (F.lmul_lt _ _ hc₀' hc) (by
            rw [F.lperm_mul hc₀' hc]
            exact B.mul_mem (hmemB c₀ hc₀) hb)
        refine ⟨F.lmul h (F.lmul c₀ c), (hk'x _).2 (Or.inr ⟨_, hc0c, rfl⟩), ?_⟩
        rw [F.lperm_mul hh (F.lmul_lt _ _ hc₀' hc), F.lperm_mul hc₀' hc, hgh, mul_assoc]

theorem pwit_cat {k : ℕ} (hk : k < F.K) :
    ∃ (as : List (Equiv.Perm (Fin 32))) (ts : List (Fin 32)), PWit (F.catSet k) as ts := by
  obtain ⟨as, ts, hlen, has, hts, hP, hQ⟩ := F.cat_wit k hk
  have hlci : ∀ i g, F.Cat k g → IsConjP i (F.lperm g) → g = F.lci i := fun i g hg hgi => by
    have hg' := F.cat_lt k hk g hg
    refine F.lperm_inj hg' (F.lci_lt i) (Equiv.ext fun x => ?_)
    have h := isConjP_unique hgi (F.lci_tab i)
    rw [h, F.lperm_apply (F.lci_lt i)]
  refine ⟨as.map F.lperm, ts, by simpa using hlen, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    exact ⟨a', has a' ha', rfl⟩
  · intro t ht
    refine ⟨F.lperm (F.lci t), ⟨_, hts t ht, rfl⟩, ?_⟩
    have h := F.lci_tab t
    intro x
    rw [F.lperm_apply (F.lci_lt t)]
    exact h x
  · intro P hP1 hP2 α ⟨g, hg, hgα⟩
    subst hgα
    refine hP (fun g => P (F.lperm g)) (fun i hi => hP1 _ ⟨_, hi, rfl⟩ i fun x => ?_)
      (fun a ha x hx hPx => ?_) g hg
    · rw [F.lperm_apply (F.lci_lt i)]
      exact F.lci_tab i x
    · rw [F.lperm_mul (F.cat_lt k hk a (has a ha)) hx]
      exact hP2 _ (List.mem_map_of_mem ha) _ (F.lperm_mem hx) hPx
  · intro Q hQ1 hQ2 i ⟨σ, ⟨g, hg, hgσ⟩, hσi⟩
    subst hgσ
    have hgi := hlci i g hg hσi
    subst hgi
    refine hQ Q (fun α hα t ht => ?_) hQ2 i hg
    have h := hQ1 _ ⟨α, hα, rfl⟩ t ht
    rwa [F.lperm_apply (F.cat_lt k hk α hα)] at h

def InCatF (S : ℕ → Prop) : Prop :=
  ∃ H : Subgroup (Equiv.Perm (Fin 32)), H ≤ autP0 ∧ IsPGroup 2 H ∧
    ∀ e, S e ↔ e < F.N ∧ F.gperm e ∈ H

noncomputable def ci (i : Fin 32) : ℕ := F.idx (F.lperm (F.lci i))

theorem lperm_lci_mem (i : Fin 32) : F.lperm (F.lci i) ∈ autP0 := F.lperm_mem (F.lci_lt i)

theorem ci_lt' (i : Fin 32) : F.ci i < F.N := F.idx_lt (F.lperm_lci_mem i)

theorem isConjP_gperm_ci (i : Fin 32) : IsConjP i (F.gperm (F.ci i)) := by
  intro x
  rw [ci, F.gperm_idx (F.lperm_lci_mem i), F.lperm_apply (F.lci_lt i)]
  exact F.lci_tab i x

theorem gperm_ci_eq {i : Fin 32} {σ : Equiv.Perm (Fin 32)} (hσ : IsConjP i σ) :
    F.gperm (F.ci i) = σ :=
  Equiv.ext fun x => congrFun (isConjP_unique (F.isConjP_gperm_ci i) hσ) x

noncomputable def iface : S5Iface where
  N := F.N
  tab := F.tab
  cm e f := F.idx (F.gperm e * F.gperm f)
  inv e := F.idx (F.gperm e)⁻¹
  ide := F.idx 1
  ci := F.ci
  InCat := F.InCatF
  complete := F.complete
  tab_inj := F.tab_inj
  cm_lt e f he hf := F.idx_lt (autP0.mul_mem (F.gperm_mem he) (F.gperm_mem hf))
  cm_tab e f he hf x := by
    rw [← F.gperm_apply (F.idx_lt (autP0.mul_mem (F.gperm_mem he) (F.gperm_mem hf))),
      F.gperm_idx (autP0.mul_mem (F.gperm_mem he) (F.gperm_mem hf)), Equiv.Perm.coe_mul,
      Function.comp_apply, F.gperm_apply he, F.gperm_apply hf]
  ide_lt := F.idx_lt autP0.one_mem
  ide_tab x := by
    rw [← F.gperm_apply (F.idx_lt autP0.one_mem), F.gperm_idx autP0.one_mem]
    rfl
  inv_lt e he := F.idx_lt (autP0.inv_mem (F.gperm_mem he))
  cm_inv e he := by
    rw [F.gperm_idx (autP0.inv_mem (F.gperm_mem he)), mul_inv_cancel]
  ci_lt := F.ci_lt'
  ci_tab i x := by
    rw [← F.gperm_apply (F.ci_lt' i)]
    exact F.isConjP_gperm_ci i x
  cat_one := by
    refine ⟨⊥, bot_le, IsPGroup.of_bot, fun e => ⟨?_, ?_⟩⟩
    · rintro rfl
      exact ⟨F.idx_lt autP0.one_mem, by rw [F.gperm_idx autP0.one_mem]; exact Subgroup.one_mem _⟩
    · rintro ⟨he, h1⟩
      rw [Subgroup.mem_bot] at h1
      rw [← h1, F.idx_gperm he]
  cat_step S hS g hg hgS hgg hgN := by
    obtain ⟨H, hHA, hHp, hSH⟩ := hS
    have hmem : ∀ σ ∈ H, F.idx σ < F.N ∧ S (F.idx σ) := fun σ hσ => by
      have h := F.idx_spec (hHA hσ)
      exact ⟨h.1, (hSH _).2 ⟨h.1, by rw [h.2]; exact hσ⟩⟩
    have hgg' : F.gperm g * F.gperm g ∈ H := by
      have h := ((hSH _).1 hgg).2
      rwa [F.gperm_idx (autP0.mul_mem (F.gperm_mem hg) (F.gperm_mem hg))] at h
    have hgN' : ∀ c ∈ H, F.gperm g * c * (F.gperm g)⁻¹ ∈ H := fun c hc => by
      obtain ⟨hc1, hc2⟩ := hmem c hc
      have h := ((hSH _).1 (hgN _ hc1 hc2)).2
      have hgc : F.gperm g * F.gperm (F.idx c) ∈ autP0 :=
        autP0.mul_mem (F.gperm_mem hg) (F.gperm_mem hc1)
      rwa [F.gperm_idx (autP0.mul_mem (F.gperm_mem (F.idx_lt hgc))
          (F.gperm_mem (F.idx_lt (autP0.inv_mem (F.gperm_mem hg))))),
        F.gperm_idx hgc, F.gperm_idx (autP0.inv_mem (F.gperm_mem hg)),
        F.gperm_idx (hHA hc)] at h
    have hN : F.gperm g ∈ Subgroup.normalizer (H : Set (Equiv.Perm (Fin 32))) :=
      Subgroup.mem_normalizer_fintype fun c hc => hgN' c hc
    obtain ⟨H', hH'⟩ := s5ext_exists_adjoin hgg' hN
    have hH'A : H' ≤ autP0 := fun x hx => by
      rcases (hH' x).1 hx with hx | ⟨b, hb, rfl⟩
      · exact hHA hx
      · exact autP0.mul_mem (F.gperm_mem hg) (hHA hb)
    refine ⟨H', hH'A, fun x => ?_, fun e => ⟨?_, ?_⟩⟩
    · have hx2 : (x : Equiv.Perm (Fin 32)) * x ∈ H := by
        rcases (hH' x).1 x.2 with hx | ⟨b, hb, hxb⟩
        · exact H.mul_mem hx hx
        · rw [hxb, show F.gperm g * b * (F.gperm g * b) =
            F.gperm g * F.gperm g * ((F.gperm g)⁻¹ * b * F.gperm g) * b by group]
          exact H.mul_mem (H.mul_mem hgg' ((Subgroup.mem_normalizer_iff''.1 hN b).1 hb)) hb
      obtain ⟨n, hn⟩ := hHp ⟨_, hx2⟩
      refine ⟨n + 1, Subtype.ext ?_⟩
      have hn' := congrArg Subtype.val hn
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at hn' ⊢
      rw [pow_succ', pow_mul, pow_two, hn']
    · rintro (he | ⟨c, hc, hcS, rfl⟩)
      · exact ⟨((hSH e).1 he).1, (hH' _).2 (Or.inl ((hSH e).1 he).2)⟩
      · have hgc : F.gperm g * F.gperm c ∈ autP0 :=
          autP0.mul_mem (F.gperm_mem hg) (F.gperm_mem hc)
        refine ⟨F.idx_lt hgc, (hH' _).2 (Or.inr ⟨_, ((hSH c).1 hcS).2, ?_⟩)⟩
        rw [F.gperm_idx hgc]
    · rintro ⟨he, heH⟩
      rcases (hH' _).1 heH with h | ⟨b, hb, hgb⟩
      · exact Or.inl ((hSH e).2 ⟨he, h⟩)
      · obtain ⟨hb1, hb2⟩ := hmem b hb
        refine Or.inr ⟨F.idx b, hb1, hb2, ?_⟩
        rw [F.gperm_idx (hHA hb), ← hgb, F.idx_gperm he]
  cat_wit S hS := by
    obtain ⟨H, hHA, hHp, hSH⟩ := hS
    have hcard : Nat.card autP0 = 2 ^ 7 * 9 := by
      rw [card_autP0 F.tab_hom F.tab_injective F.complete F.tab_inj, F.N_eq]
    obtain ⟨s, hs, hsH⟩ := exists_conj_le hcard (by decide) F.S0_le F.card_S0 hHA hHp
    let R : Subgroup (Equiv.Perm (Fin 32)) := H.comap (MulAut.conj s).toMonoidHom
    have hRmem : ∀ y, y ∈ R ↔ s * y * s⁻¹ ∈ H := fun y => Iff.rfl
    have hRS : R ≤ F.S0 := fun y hy => by
      have h := hsH _ ((hRmem y).1 hy)
      simpa [mul_assoc] using h
    obtain ⟨k, hk, hRk⟩ := F.cat_complete' R hRS
    obtain ⟨as, ts, hw⟩ := F.pwit_cat hk
    have hw' := pwit_conj hw hs
    have hset : {x | s⁻¹ * x * s ∈ F.catSet k} = (H : Set (Equiv.Perm (Fin 32))) := by
      ext x
      rw [Set.mem_setOf_eq, ← hRk, SetLike.mem_coe, hRmem, SetLike.mem_coe]
      simp [mul_assoc]
    rw [hset] at hw'
    obtain ⟨hlen, has, hts, hP, hQ⟩ := hw'
    refine ⟨(as.map fun a => s * a * s⁻¹).map F.idx, ts.map s, by simpa using hlen, ?_, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      have h := F.idx_spec (hHA (has a' ha'))
      exact ⟨h.1, (hSH _).2 ⟨h.1, by rw [h.2]; exact has a' ha'⟩⟩
    · intro t ht
      obtain ⟨σ, hσ, hσt⟩ := hts t ht
      have h := F.gperm_ci_eq hσt
      exact (hSH _).2 ⟨F.idx_lt (F.lperm_lci_mem t), by rw [h]; exact hσ⟩
    · intro P hP1 hP2 α hα hSα
      have h := hP (fun σ => P (F.idx σ))
        (fun σ hσ i hi => by
          have h1 := F.gperm_ci_eq hi
          have h2 : F.idx σ = F.ci i := by
            rw [← h1, F.idx_gperm (F.ci_lt' i)]
          rw [h2]
          exact hP1 i ((hSH _).2 ⟨F.idx_lt (F.lperm_lci_mem i), by rw [h1]; exact hσ⟩))
        (fun a ha x hx hPx => by
          have h1 := hP2 (F.idx a) (List.mem_map_of_mem ha) (F.idx x) (F.idx_lt hx) hPx
          have haA : a ∈ autP0 := hHA (has a ha)
          rwa [F.gperm_idx haA, F.gperm_idx hx] at h1)
        (F.gperm α) ((hSH α).1 hSα).2
      rwa [F.idx_gperm hα] at h
    · intro Q hQ1 hQ2 i hSi
      refine hQ Q (fun α hα t ht => ?_) hQ2 i ⟨F.gperm (F.ci i), ((hSH _).1 hSi).2,
        F.isConjP_gperm_ci i⟩
      have h := hQ1 (F.idx α) (F.idx_lt (hHA hα))
        ((hSH _).2 ⟨F.idx_lt (hHA hα), by rw [F.gperm_idx (hHA hα)]; exact hα⟩) t ht
      rwa [← F.gperm_apply (F.idx_lt (hHA hα)), F.gperm_idx (hHA hα)] at h

end S5KFacts

end CertificateChecks.S5K
