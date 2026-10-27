module

public import Certificates.Kernel.VecCert.WordProg

public section

namespace CertificateChecks.KernelWPX

open CFSG.KC.Ord CFSG.KC.WP CFSG.KS.Ord CertificateChecks.KernelHomG CertificateChecks.KernelWP
  CFSG.Sporadic.Bridge

variable {d : Nat} {K : Type} [CommRing K] {Q : Nat → Prop} {Mt : Nat → Matrix (Fin d) (Fin d) K}
  {mul : Nat → Nat → Nat} {vld : Nat → Bool} {ONE : Nat} {RB : Nat → Nat} {L : Nat}

theorem inv_val (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {u : GL (Fin d) K} {g : Nat} (hg : g < L)
    (hu : u.val = Mt (RB (g + 1))) : (u⁻¹ : GL (Fin d) K).val = Mt (RB (L + 1 + g)) := by
  have h := pair_of_invsG hs hroot hinv g hg
  rw [← hu] at h
  calc (u⁻¹ : GL (Fin d) K).val = (u⁻¹ : GL (Fin d) K).val * (u.val * Mt (RB (L + 1 + g))) := by
        rw [h, mul_one]
    _ = Mt (RB (L + 1 + g)) := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem val_wordProd (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {x : Nat → GL (Fin d) K}
    (hx : ∀ g < L, (x g).val = Mt (RB (g + 1))) {v : List (Nat × Bool)} (hv : ∀ l ∈ v, l.1 < L) :
    (wordProd x v).val = (v.map fun l => Mt (letM RB L l)).prod := by
  rw [wordProd, ← Units.coeHom_apply, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨g, s⟩ hl
  have hg := hv _ hl
  cases s
  · simp only [Function.comp_apply, Units.coeHom_apply, Bool.false_eq_true, ↓reduceIte]
    rw [inv_val hs hroot hinv hg (hx g hg)]
    rfl
  · simp only [Function.comp_apply, Units.coeHom_apply, ↓reduceIte]
    rw [hx g hg]
    rfl

theorem prod_eq_wordMat (v : List (Nat × Bool)) :
    (v.map fun l => Mt (letM RB L l)).prod = wordMat Mt RB L (v.map codeOf) := by
  unfold wordMat
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, letC_codeOf]

theorem units_of_cover (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (L + 1) = true) (hinv : invsOK RB mul vld L ONE = true)
    {rels : List (List (Nat × Bool))} (hb : relsBounded rels L = true)
    (hrel : ∀ v ∈ rels, (v.map fun l => Mt (letM RB L l)).prod = 1) {S : Nat}
    (hregs : RegsInG Q Mt L RB S) :
    ∃ x : Nat → GL (Fin d) K, (∀ g < L, (x g).val = Mt (RB (g + 1))) ∧ (∀ g, L ≤ g → x g = 1) ∧
      (∀ v ∈ rels, wordProd x v = 1) ∧
      ∀ r, 0 < r → r < S → ∀ u : GL (Fin d) K, u.val = Mt (RB r) →
        u ∈ Subgroup.closure (x '' Set.Iio L) := by
  have hX := pair_of_invsG hs hroot hinv
  have hXl : ∀ g < L, Mt (RB (L + 1 + g)) * Mt (RB (g + 1)) = 1 := fun g hg =>
    mul_eq_one_comm.mp (hX g hg)
  let x : Nat → GL (Fin d) K := fun g =>
    if hg : g < L then ⟨Mt (RB (g + 1)), Mt (RB (L + 1 + g)), hX g hg, hXl g hg⟩ else 1
  have hx : ∀ g < L, (x g).val = Mt (RB (g + 1)) := by
    intro g hg
    simp [x, hg]
  refine ⟨x, hx, fun g hg => by simp [x, Nat.not_lt.2 hg], fun v hv => ?_, ?_⟩
  · apply Units.ext
    rw [val_wordProd hs hroot hinv hx (relsBounded_spec hb v hv), Units.val_one, hrel v hv]
  · have hcl : ∀ M ∈ Submonoid.closure (rootSetG Mt L RB),
        ∃ u ∈ Subgroup.closure (x '' Set.Iio L), u.val = M := by
      intro M hM
      induction hM using Submonoid.closure_induction with
      | mem M hM =>
        obtain ⟨g, hg0, hg2, rfl⟩ := hM
        rcases Nat.lt_or_ge L g with hgl | hgl
        · refine ⟨(x (g - L - 1))⁻¹,
            Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g - L - 1, by
              change g - L - 1 < L
              omega, rfl⟩), ?_⟩
          rw [inv_val hs hroot hinv (by omega) (hx _ (by omega))]
          have e : L + 1 + (g - L - 1) = g := by omega
          rw [e]
        · refine ⟨x (g - 1), Subgroup.subset_closure ⟨g - 1, by
            change g - 1 < L
            omega, rfl⟩, ?_⟩
          rw [hx _ (by omega)]
          have e : g - 1 + 1 = g := by omega
          rw [e]
      | one => exact ⟨1, Subgroup.one_mem _, rfl⟩
      | mul M N _ _ hM hN =>
        obtain ⟨u, hu, rfl⟩ := hM
        obtain ⟨v, hv, rfl⟩ := hN
        exact ⟨u * v, Subgroup.mul_mem _ hu hv, rfl⟩
    intro r hr0 hrS u hu
    obtain ⟨w, hw, hval⟩ := hcl _ (hregs r hr0 hrS).2
    have e : u = w := Units.ext (by rw [hu, ← hval])
    rw [e]
    exact hw

end CertificateChecks.KernelWPX

end
