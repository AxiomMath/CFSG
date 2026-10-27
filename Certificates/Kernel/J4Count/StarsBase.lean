
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4QuotBase
public import Certificates.Kernel.J4Q.Mat

@[expose] public section

namespace CertificateChecks.KernelJ4Count.Stars

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CertificateChecks.KernelJ4Q

theorem starOK_gen {k : ℕ} (hk : k < 3) {i : ℕ} (hi : i < 24) :
    StarOK (xJ k) i ((starPermOf k).getD i 0) := by
  intro c hc
  obtain ⟨-, -, hact⟩ := star_perm_facts k hk
  have hℓ : ((k : ℤ) + 1) ∈ letters := by interval_cases k <;> simp [letters]
  have hx : XJ ((k : ℤ) + 1) = xJ k := by
    interval_cases k
    · simpa using XJ_one
    · simpa using XJ_two
    · simpa using XJ_three
  refine ⟨act ((k : ℤ) + 1) c, hact i hi c hc, ?_⟩
  rw [← hx]
  exact hX_all matFacts hℓ c

theorem starOK_closure : ∀ g ∈ Hj, ∀ i < 24, ∃ i' < 24, StarOK g i i' := by
  intro g hg
  have hg' : g ∈ Submonoid.closure ({xJ 0, xJ 1, xJ 2} : Set J) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact fun i hi => ⟨_, (star_perm_facts 0 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
    · exact fun i hi => ⟨_, (star_perm_facts 1 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
    · exact fun i hi => ⟨_, (star_perm_facts 2 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
  | one => exact fun i hi => ⟨i, hi, starOK_one i⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨i', hi', h1⟩ := hy i hi
    obtain ⟨i'', hi'', h2⟩ := hx i' hi'
    exact ⟨i'', hi'', starOK_mul h1 h2⟩

theorem starOK_unique {g : J} {i i' i'' : ℕ} (hi : i < 24) (hi' : i' < 24) (hi'' : i'' < 24)
    (h1 : StarOK g i i') (h2 : StarOK g i i'') : i' = i'' := by
  by_contra hne
  obtain ⟨-, -, -, hdis, hint, -⟩ := star_facts
  obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := hdis i hi
  obtain ⟨d₁, hd₁, e₁⟩ := h1 c₁ hc₁
  obtain ⟨d₁', hd₁', e₁'⟩ := h2 c₁ hc₁
  obtain ⟨d₂, hd₂, e₂⟩ := h1 c₂ hc₂
  obtain ⟨d₂', hd₂', e₂'⟩ := h2 c₂ hc₂
  have hM := matFacts
  have hd1 : d₁ = d₁' :=
    eta_inj hM d₁ (mem_star_lt hi' hd₁) d₁' (mem_star_lt hi'' hd₁') (e₁.symm.trans e₁')
  have hd2 : d₂ = d₂' :=
    eta_inj hM d₂ (mem_star_lt hi' hd₂) d₂' (mem_star_lt hi'' hd₂') (e₂.symm.trans e₂')
  have hd12 : d₁ ≠ d₂ := by
    intro h
    apply hc12
    have : eta uJ 11 c₁ = eta uJ 11 c₂ := by
      have h3 : g * eta uJ 11 c₁ * g⁻¹ = g * eta uJ 11 c₂ * g⁻¹ := by rw [e₁, e₂, h]
      simpa using h3
    exact eta_inj hM c₁ (mem_star_lt hi hc₁) c₂ (mem_star_lt hi hc₂) this
  exact hd12 (hint i' hi' i'' hi'' hne d₁ hd₁ (hd1 ▸ hd₁') d₂ hd₂ (hd2 ▸ hd₂'))

noncomputable def starMap (g : Hj) (i : Fin 24) : Fin 24 :=
  ⟨(starOK_closure g.1 g.2 i i.2).choose, (starOK_closure g.1 g.2 i i.2).choose_spec.1⟩

theorem starMap_spec (g : Hj) (i : Fin 24) : StarOK (g : J) i (starMap g i) :=
  (starOK_closure g.1 g.2 i i.2).choose_spec.2

theorem starMap_eq {g : Hj} {i i' : Fin 24} (h : StarOK (g : J) i i') : starMap g i = i' :=
  Fin.ext (starOK_unique i.2 (starMap g i).2 i'.2 (starMap_spec g i) h)

theorem starMap_mul (g h : Hj) (i : Fin 24) : starMap (g * h) i = starMap g (starMap h i) :=
  starMap_eq (starOK_mul (starMap_spec h i) (starMap_spec g (starMap h i)))

theorem starMap_one (i : Fin 24) : starMap 1 i = i :=
  starMap_eq (by simpa using starOK_one i)

@[expose] noncomputable def starHom : Hj →* Equiv.Perm (Fin 24) where
  toFun g :=
    { toFun := starMap g
      invFun := starMap g⁻¹
      left_inv := fun i => by rw [← starMap_mul, inv_mul_cancel, starMap_one]
      right_inv := fun i => by rw [← starMap_mul, mul_inv_cancel, starMap_one] }
  map_one' := by ext i; exact congrArg Fin.val (starMap_one i)
  map_mul' g h := by ext i; exact congrArg Fin.val (starMap_mul g h i)

theorem starHom_apply (g : Hj) (i : Fin 24) : starHom g i = starMap g i := rfl

theorem starHom_xJ {k : ℕ} (hk : k < 3) : starHom ⟨xJ k, xJ_mem hk⟩ = tauOf k := by
  ext i
  have h := starMap_eq (g := ⟨xJ k, xJ_mem hk⟩) (i := i)
    (i' := ⟨(starPermOf k).getD i 0, (star_perm_facts k hk).2.1 i i.2⟩) (starOK_gen hk i.2)
  have h2 := (tau_facts k hk).1 i
  change (starMap ⟨xJ k, xJ_mem hk⟩ i : ℕ) = (tauOf k i : ℕ)
  rw [h, h2]

theorem range_starHom : starHom.range = Subgroup.closure {tauOf 0, tauOf 1, tauOf 2} := by
  have htop : Subgroup.closure ((((↑) : Hj → J)) ⁻¹' ({xJ 0, xJ 1, xJ 2} : Set J)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with h | h | h
    · have : x = ⟨xJ 0, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]
      exact Or.inl rfl
    · have : x = ⟨xJ 1, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]
      exact Or.inr (Or.inl rfl)
    · have : x = ⟨xJ 2, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]
      exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨xJ 0, xJ_mem (by norm_num)⟩, Or.inl rfl, starHom_xJ (by norm_num)⟩
    · exact ⟨⟨xJ 1, xJ_mem (by norm_num)⟩, Or.inr (Or.inl rfl), starHom_xJ (by norm_num)⟩
    · exact ⟨⟨xJ 2, xJ_mem (by norm_num)⟩, Or.inr (Or.inr rfl), starHom_xJ (by norm_num)⟩

end CertificateChecks.KernelJ4Count.Stars

end
