module

public import Certificates.Kernel.Misc.A6GL4.K
public import Certificates.Kernel.Misc.GL4.EAFacts
public import CFSG.Certificates.Kernel.Misc.A6GL4Sound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.A6GL4

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.A6GL4
open CFSG.KC.Misc.Clos (ExactList treeAt sortAt closedAt)
open CertificateChecks.KernelMisc.GL4EA (EA EAI eaAt eaAt_ok ea_exact)
open Certificates.A5GL42 (Mat4 ofCode)
open Certificates.GL4 (GL4 sg)
open Certificates.Asc82NormA6

theorem rhoCode_sigma : rhoCode sigma = xA6 := by decide +kernel

theorem rhoCode_tau : rhoCode tau = yA6 := by decide +kernel

theorem enc_x : enc4 (rhoU sigma) = xA6 := by rw [enc4_rhoU, rhoCode_sigma]

theorem enc_y : enc4 (rhoU tau) = yA6 := by rw [enc4_rhoU, rhoCode_tau]

theorem gens_ex : ∀ c ∈ [xA6, yA6], ∃ g : GL4, enc4 g = c := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨_, enc_x⟩
  · exact ⟨_, enc_y⟩

theorem clos_ok (k : ℕ) (hk : k < 360) :
    treeAt mul4F id4 gH 2 HE HP k = true ∧ sortAt 360 HE HS k = true ∧
      closedAt mul4F gH 2 360 HE HC k = true := by
  have h := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 (CK.all 0 (by norm_num)) k (Nat.zero_le k)
    (by change k < 0 + 360; omega)
  obtain ⟨a, h⟩ := andB_iff.1 h
  obtain ⟨b, c⟩ := andB_iff.1 h
  exact ⟨a, b, c⟩

theorem sorted : ∀ i < 360, sortAt 360 HE HS i = true := fun i hi => (clos_ok i hi).2.1

theorem h_exact : Nat.card (sg [xA6, yA6]) = 360 ∧ ExactList enc4 (sg [xA6, yA6]) 360 HE :=
  sg_exact_of [xA6, yA6] gens_ex (G := gH) (PA := HP) (SG := HS) (CT := HC)
    (fun j _ => lAt_eq [xA6, yA6] j) (by norm_num) (fun k hk => (clos_ok k hk).1) sorted
    (fun k hk => (clos_ok k hk).2.2)

theorem u4_x : u4 xA6 = rhoU sigma := gl4_enc.inj (by rw [enc4_u4 ⟨_, enc_x⟩, enc_x])

theorem u4_y : u4 yA6 = rhoU tau := gl4_enc.inj (by rw [enc4_u4 ⟨_, enc_y⟩, enc_y])

theorem sigma_mem : sigma ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem tau_mem : tau ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem sg_eq_map :
    sg [xA6, yA6] = (Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6)))).map rhoU := by
  rw [sg_eq_of _ gens_ex, MonoidHom.map_closure, Set.image_pair]
  congr 1
  ext g
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, u4_x, u4_y]

theorem closure_eq :
    Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) = alternatingGroup (Fin 6) := by
  have hle : Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact sigma_mem
    · exact tau_mem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := h_exact.1
  rw [sg_eq_map, Subgroup.card_map_of_injective rhoU_injective] at h1
  rw [h1, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem h_eq : sg [xA6, yA6] = (alternatingGroup (Fin 6)).map rhoU := by
  rw [sg_eq_map, closure_eq]

theorem a_exact : ExactList enc4 ((alternatingGroup (Fin 6)).map rhoU) 360 HE := by
  rw [← h_eq]
  exact h_exact.2

theorem ea_inv : ∀ k < 20160, ∀ g : GL4, enc4 g = EA k → enc4 g⁻¹ = EAI k := by
  intro k hk g hg
  have h := (andB_iff.1 (eaAt_ok k hk)).1
  rw [← hg] at h
  exact enc4_inv_of_invW h

theorem y_ok : ∀ k < 20160, yAt EA EAI W yA6 k = true :=
  CFSG.KC.Misc.Clos.forall_of_chunks 5040 4 _ fun c hc => YK.all c hc

theorem x_ok : ∀ k < 20160, xAt EA EAI W HE yA6 k = true :=
  CFSG.KC.Misc.Clos.forall_of_chunks 5040 4 _ fun c hc => XK.all c hc

theorem mem_a {h : GL4} (hh : h ∈ (alternatingGroup (Fin 6)).map rhoU) :
    ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ rhoU a = h := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hh
  exact ⟨a, Equiv.Perm.mem_alternatingGroup.1 ha, rfl⟩

theorem classify : ∀ x y : Mat4, Certificates.Asc82NormA6.Rel x y → x ≠ 1 →
    ∃ c c' : Mat4, c * c' = 1 ∧ (∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ rho a = c' * x * c) ∧
      ∃ b : Equiv.Perm (Fin 6), b.sign = 1 ∧ rho b = c' * y * c := by
  intro x y hxy hx1
  have hx3 : x ^ 3 = 1 := hxy.1
  have hy5 : y ^ 5 = 1 := hxy.2.1
  let ux : GL4 := ⟨x, x ^ 2, by rw [← pow_succ']; exact hx3, by rw [← pow_succ]; exact hx3⟩
  let uy : GL4 := ⟨y, y ^ 4, by rw [← pow_succ']; exact hy5, by rw [← pow_succ]; exact hy5⟩
  have hrel : Certificates.Asc82NormA6.Rel ux uy := (rel_map (Units.coeHom Mat4) Units.val_injective ux uy).1 hxy
  have hux : ux ≠ 1 := fun e => hx1 (congrArg Units.val e)
  have huy : uy ≠ 1 := fun e => hux (eq_one_of_rel_one (e ▸ hrel))
  obtain ⟨g, hg⟩ := yAt_sound ea_exact ea_inv y_ok uy huy hrel.2.1
  have hrel' : Certificates.Asc82NormA6.Rel (g⁻¹ * ux * g) (g⁻¹ * uy * g) := by
    have := (rel_conj g⁻¹ ux uy).2 hrel
    rwa [inv_inv] at this
  have hx1' : g⁻¹ * ux * g ≠ 1 := by
    intro e
    apply hux
    have : ux = g * (g⁻¹ * ux * g) * g⁻¹ := by group
    rw [this, e, mul_one, mul_inv_cancel]
  obtain ⟨c, hc1, hc2⟩ := xAt_sound ea_exact ea_inv a_exact x_ok hg _ hx1' hrel'
  obtain ⟨a, ha, ea⟩ := mem_a hc1
  obtain ⟨b, hb, eb⟩ := mem_a hc2
  refine ⟨((g * c : GL4) : Mat4), (((g * c)⁻¹ : GL4) : Mat4), by rw [← Units.val_mul,
    mul_inv_cancel, Units.val_one], ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
  · rw [← rhoU_val, ea]
    have e : c⁻¹ * (g⁻¹ * ux * g) * c = (g * c)⁻¹ * ux * (g * c) := by group
    rw [e]
    rfl
  · rw [← rhoU_val, eb]
    have e : c⁻¹ * (g⁻¹ * uy * g) * c = (g * c)⁻¹ * uy * (g * c) := by group
    rw [e]
    rfl

theorem normalizer_le :
    Subgroup.normalizer (((alternatingGroup (Fin 6)).map rhoU : Subgroup GL4) : Set GL4) ≤
      rhoU.range := by
  have hS : rhoU.range ≤
      Subgroup.normalizer (((alternatingGroup (Fin 6)).map rhoU : Subgroup GL4) : Set GL4) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (alternatingGroup (Fin 6)).Normal)]
    exact Subgroup.le_normalizer_map rhoU
  have hcard : Nat.card rhoU.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective rhoU_injective).toEquiv, Nat.card_perm,
      Nat.card_fin]
    decide
  have hx : rhoU sigma ∈ (alternatingGroup (Fin 6)).map rhoU := Subgroup.mem_map_of_mem _ sigma_mem
  have hy : rhoU tau ∈ (alternatingGroup (Fin 6)).map rhoU := Subgroup.mem_map_of_mem _ tau_mem
  obtain ⟨c, hc⟩ := djB_sound a_exact sorted (DK.all 0 (by norm_num)) enc_x enc_y hx hy
  refine normalizer_le_of hS hcard c fun l hl k hk hm => ?_
  rcases hc l hl k hk with h | h
  · exact h ((Subgroup.mem_normalizer_iff.1 hm _).1 hx)
  · exact h ((Subgroup.mem_normalizer_iff.1 hm _).1 hy)

theorem complete : ∀ g : Mat4, (∃ g' : Mat4, g * g' = 1) →
    (∀ a : Equiv.Perm (Fin 6), a.sign = 1 →
      ∃ a' : Equiv.Perm (Fin 6), a'.sign = 1 ∧ g * rho a = rho a' * g) →
    ∃ p : Equiv.Perm (Fin 6), rho p = g := by
  intro g ⟨g', hgg'⟩ hn
  let u : GL4 := ⟨g, g', hgg', mul_eq_one_comm.mp hgg'⟩
  have hu : u ∈
      Subgroup.normalizer (((alternatingGroup (Fin 6)).map rhoU : Subgroup GL4) : Set GL4) := by
    refine mem_normalizer_of_conj u fun h hh => ?_
    obtain ⟨a, ha, rfl⟩ := mem_a hh
    obtain ⟨a', ha', e⟩ := hn a ha
    have : u * rhoU a * u⁻¹ = rhoU a' := by
      apply Units.ext
      change g * rho a * g' = rho a'
      rw [e, mul_assoc, hgg', mul_one]
    rw [this]
    exact Subgroup.mem_map_of_mem _ (Equiv.Perm.mem_alternatingGroup.2 ha')
  obtain ⟨p, hp⟩ := normalizer_le hu
  exact ⟨p, congrArg Units.val hp⟩

theorem facts : Facts where
  rho_one := rho_one'
  rho_mul := rho_mul'
  rho_ker := rho_ker'
  sigma_even := by decide
  tau_even := by decide
  rel := by
    refine (rel_map rhoU rhoU_injective sigma tau).1 ((relB_iff _ _).1 ?_)
    rw [enc_x, enc_y]
    decide +kernel
  gen := by
    intro a ha
    rw [closure_eq]
    exact Equiv.Perm.mem_alternatingGroup.2 ha
  classify := classify
  complete := complete

end CertificateChecks.KernelMisc.A6GL4

end
