module

public import Certificates.Kernel.LyBase.Facts

public section

namespace CertificateChecks.KernelLyDce

open Equiv MulAction CFSG.KC.LyBase CertificateChecks.KernelLyBase CertificateChecks.KernelLy
  CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable

abbrev S5 : List (Fin 6) := subsetOf 6 [0, 1, 2, 3, 4]

theorem renumber_some {m : Nat} (S : List (Fin m)) :
    ∀ w : List (Fin m × Bool), (∀ l ∈ w, l.1 ∈ S) → ∃ w', renumber S w = some w'
  | [], _ => ⟨[], rfl⟩
  | l :: w, h => by
    obtain ⟨w', hw'⟩ := renumber_some S w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    cases hi : S.finIdxOf? l.1 with
    | none =>
      rw [List.finIdxOf?_eq_none_iff] at hi
      exact absurd (h l List.mem_cons_self) hi
    | some i => exact ⟨(i, l.2) :: w', by simp [renumber, hi, hw']⟩

theorem mem_S5 : ∀ i : Fin 6, i.val < 5 → i ∈ S5 := by decide

theorem lift_renumber {H : Type*} [Group H] {m : Nat} (S : List (Fin m)) (g : Fin m → H)
    {w : List (Fin m × Bool)} {w' : List (Fin S.length × Bool)} (h : renumber S w = some w') :
    FreeGroup.lift (fun j => g (S.get j)) (FreeGroup.mk w') = FreeGroup.lift g (FreeGroup.mk w) := by
  rw [lift_comp_mk, map_renumber S w w' h]

theorem rb5_rel {H : Type*} [Group H] (g : Fin 6 → H)
    (hg : ∀ r ∈ RB, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin S5.length) | r ∈ RB5.map FreeGroup.mk},
      FreeGroup.lift (fun j => g (S5.get j)) r = 1 := by
  intro r hr
  simp only [Set.mem_setOf_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
  obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
  rw [lift_renumber S5 g hren]
  exact hg w hw

theorem lift_of_eq_mk {m : Nat} (rels : Set (FreeGroup (Fin m))) (x : FreeGroup (Fin m)) :
    FreeGroup.lift (fun i => (PresentedGroup.of i : PresentedGroup rels)) x =
      PresentedGroup.mk rels x := by
  have e : FreeGroup.lift (fun i => (PresentedGroup.of i : PresentedGroup rels)) =
      PresentedGroup.mk rels := by
    apply FreeGroup.ext_hom
    intro i
    simp [PresentedGroup.of]
  rw [e]

theorem hom_lift {A B : Type*} [Group A] [Group B] {m : Nat} (φ : A →* B) (f : Fin m → A)
    (x : FreeGroup (Fin m)) : φ (FreeGroup.lift f x) = FreeGroup.lift (fun i => φ (f i)) x := by
  have e : φ.comp (FreeGroup.lift f) = FreeGroup.lift fun i => φ (f i) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact congrArg (fun F : FreeGroup (Fin m) →* B => F x) e

section Base

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat))
include hc hd

theorem card_B0_ge : 5388768000 ≤ Nat.card Ly0.B0 := by
  have e₀ := ncard_orbit_mul_card_inf Ly0.B0 p0
  have e₁ := ncard_orbit_mul_card_inf (Ly0.B0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p0) p3
  have e₂ := ncard_orbit_mul_card_inf
    (Ly0.B0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p3) p1
  have h₀ := orbit0_le hc hd
  have h₁ := orbit1_le hc hd
  have h₂ := orbit2_le hc hd
  have hpos : 0 < Nat.card ↥(Ly0.B0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p0 ⊓
      stabilizer (Perm (Fin Ly0.deg)) p3 ⊓ stabilizer (Perm (Fin Ly0.deg)) p1) := Nat.card_pos
  rw [← e₀, ← e₁, ← e₂]
  calc 5388768000 = 66825 * (20160 * (4 * 1)) := by norm_num
    _ ≤ _ := Nat.mul_le_mul h₀ (Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ hpos))

noncomputable def rb5ToB0 : PG _ RB5 →* Ly0.B0 :=
  PresentedGroup.toGroup (rb5_rel gBs fun r hr => Subtype.ext (by
    rw [coe_lift_gBs]
    exact rb_eq_one hc hd r hr))

theorem rb5ToB0_surjective : Function.Surjective (rb5ToB0 hc hd) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← Subgroup.closure_closure_coe_preimage,
    Subgroup.closure_le]
  rintro ⟨x, hx⟩ hx'
  have e0 : S5.get ⟨0, by decide⟩ = 0 := by decide
  have e1 : S5.get ⟨1, by decide⟩ = 1 := by decide
  have g0 : gB 0 = Ly0.cG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]
  have g1 : gB 1 = Ly0.dG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]
  rcases hx' with h | h
  · refine ⟨PresentedGroup.of ⟨0, by decide⟩, ?_⟩
    rw [rb5ToB0, PresentedGroup.toGroup.of, e0]
    exact Subtype.ext (g0.trans h.symm)
  · refine ⟨PresentedGroup.of ⟨1, by decide⟩, ?_⟩
    rw [rb5ToB0, PresentedGroup.toGroup.of, e1]
    exact Subtype.ext (g1.trans (Set.mem_singleton_iff.1 h).symm)

theorem rb5ToB0_injective (hbc : RB5Bound) : Function.Injective (rb5ToB0 hc hd) := by
  have : Finite (PG _ RB5) := hbc.1
  exact ((rb5ToB0_surjective hc hd).bijective_of_nat_card_le
    (hbc.2.trans (card_B0_ge hc hd))).1

theorem lift_of_eq_one_of_wB (hbc : RB5Bound) {R : List (List (Fin 6 × Bool))}
    (hB : ∀ r ∈ RB, r ∈ R) {w : List (Fin 6 × Bool)} (h : wB w = true) :
    FreeGroup.lift (fun i => (PresentedGroup.of i : PG 6 R)) (FreeGroup.mk w) = 1 := by
  have hb := (bFix_sound (cF := cL) (dF := dL) (bs := base) h).1
  obtain ⟨w', hw'⟩ := renumber_some S5 w fun l hl =>
    mem_S5 l.1 ((isBWord_iff w).1 hb l hl)
  have hR : ∀ r ∈ RB, FreeGroup.lift (fun i => (PresentedGroup.of i : PG 6 R))
      (FreeGroup.mk r) = 1 := fun r hr => by
    rw [lift_of_eq_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hB r hr))
  let ψ : PG _ RB5 →* PG 6 R := PresentedGroup.toGroup (rb5_rel _ hR)
  set x : PG _ RB5 := FreeGroup.lift (fun j => (PresentedGroup.of j : PG _ RB5)) (FreeGroup.mk w')
  have hx : rb5ToB0 hc hd x = 1 := by
    rw [hom_lift]
    have e : (fun j => rb5ToB0 hc hd (PresentedGroup.of j)) = fun j => gBs (S5.get j) := by
      funext j
      rw [rb5ToB0, PresentedGroup.toGroup.of]
    rw [e, lift_renumber S5 gBs hw']
    exact lift_gBs_of_wB hc hd hbc h
  have hx1 : x = 1 := rb5ToB0_injective hc hd hbc (hx.trans (map_one _).symm)
  have hψ : ψ x = FreeGroup.lift (fun i => (PresentedGroup.of i : PG 6 R)) (FreeGroup.mk w) := by
    rw [hom_lift]
    have e : (fun j => ψ (PresentedGroup.of j : PG _ RB5)) =
        fun j => (PresentedGroup.of (S5.get j) : PG 6 R) := by
      funext j
      exact PresentedGroup.toGroup.of (rb5_rel _ hR)
    rw [e, lift_renumber S5 _ hw']
  rw [← hψ, hx1, map_one]

end Base

end CertificateChecks.KernelLyDce

end
