module

public import Certificates.Kernel.PropA.CoverRed
public import Certificates.Kernel.PropA.Enum
public import Certificates.Kernel.PropA.FactChk
public import CFSG.Certificates.Kernel.Spor.PMemSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
import CFSG.ClassicalGroups.Orthogonal.Derived

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PMem CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA
open scoped commutatorElement

theorem pa450010_comm_le_self (H : Subgroup (Perm (Fin 28))) : ⁅H, H⁆ ≤ H :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] noncomputable def pa450010cl (b : Bool) (kS : ℕ) (ws : List (List Int)) :
    Subgroup (Perm (Fin 28)) :=
  closure ((fun j => pa450010wv b kS ws[j]!) '' {j | j < ws.length})

@[expose] noncomputable def pa450010Jg : Subgroup (Perm (Fin 28)) := pa450010cl false 2 pa450010wJ

theorem pa450010_gen_mem (b : Bool) (kS : ℕ) (ws : List (List Int)) {j : ℕ} (hj : j < ws.length) :
    pa450010wv b kS ws[j]! ∈ pa450010cl b kS ws :=
  subset_closure ⟨j, hj, rfl⟩

theorem pa450010_rec {b : Bool} {kS N k cnt : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {ws : List (List Int)} (hkS : kS ≤ 4)
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) N k G GI cnt T PL kS
      (pa450010S b) (pa450010SI b) ws = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 N = true) :
    ∃ x : ℕ → Perm (Fin 28), (∀ i < cnt, PRep 28 5 (T i) (x i)) ∧ cnt = N ∧
      (∀ y, y ∈ pa450010cl b kS ws ↔ ∃ i < cnt, x i = y) ∧
      Nat.card (pa450010cl b kS ws) = N ∧ k = ws.length ∧
      (∀ j < k, PRep 28 5 (G j) (pa450010wv b kS ws[j]!)) ∧
      (∀ j < k, PRep 28 5 (GI j) (pa450010wv b kS ws[j]!)⁻¹) := by
  obtain ⟨x, hx, -, hN, hmem, hcard⟩ := pa450010_left hkS hd hsl
  obtain ⟨-, -, hk, hg, hgi⟩ := recHdK_gens (by norm_num) (by norm_num)
    (pa450010_prepSk b hkS) (pa450010_prepSIk b hkS) hd
  exact ⟨x, hx, hN, hmem, hcard.trans hN, hk, hg, hgi⟩

theorem pa450010_prepX : PRep 28 5 pa450010XD.R pa450010x := by
  have h := pa450010_root (b := false) (kS := 2) (by norm_num) pa450010_XD_root
  rwa [pa450010wv_wx false le_rfl] at h

theorem pa450010_x_memD : pa450010x ∈ D28 := by
  rw [← pa450010wv_wx false (le_refl 2)]
  exact pa450010wv_memD false _

theorem pa450010_cl_le_cent {b : Bool} {kS k : ℕ} {G : ℕ → ℕ} {ws : List (List Int)}
    (hk : k = ws.length) (hg : ∀ j < k, PRep 28 5 (G j) (pa450010wv b kS ws[j]!))
    (hc : centK 28 5 (mask 5) (28 * 5) k G pa450010XD.R = true) :
    pa450010cl b kS ws ≤ centralizer ({pa450010x} : Set (Perm (Fin 28))) := by
  have h := closure_le_centralizer (by norm_num) hg pa450010_prepX hc
  subst hk
  exact h

theorem pa450010_card_Dx :
    Nat.card ↥(D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) = 240 := by
  obtain ⟨c, -, hinj, hN, hcls⟩ := pa450010_conj (b := false) (by norm_num) pa450010_prepX
    pa450010_XD_hd pa450010_XD_sl
  rw [pa450010_clD] at hcls
  have h := pa450010_size pa450010_x_memD hcls hinj
  rw [hN, card_D28] at h
  omega

theorem pa450010_E_eq :
    D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) = pa450010cl false 2 pa450010wCDX := by
  obtain ⟨-, -, -, -, hcard, hk, hg, -⟩ := pa450010_rec (b := false) (by norm_num) pa450010_CDX_hd
    pa450010_CDX_sl
  have hle : pa450010cl false 2 pa450010wCDX ≤
      D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) :=
    le_inf ((closure_le _).2 (by rintro _ ⟨j, -, rfl⟩; exact pa450010wv_memD false _))
      (pa450010_cl_le_cent hk hg pa450010_CDX_cent)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [pa450010_card_Dx, hcard])).symm

theorem pa450010_J_rec : ∃ x : ℕ → Perm (Fin 28), (∀ i < pa450010J.cnt, PRep 28 5 (pa450010J.T i) (x i)) ∧
      pa450010J.cnt = 60 ∧ (∀ y, y ∈ pa450010Jg ↔ ∃ i < pa450010J.cnt, x i = y) ∧
      Nat.card pa450010Jg = 60 ∧ pa450010J.k = 2 ∧
      (∀ j < 2, PRep 28 5 (pa450010J.G j) (pa450010wv false 2 pa450010wJ[j]!)) ∧
      (∀ j < 2, PRep 28 5 (pa450010J.GI j) (pa450010wv false 2 pa450010wJ[j]!)⁻¹) := by
  obtain ⟨x, hx, hN, hmem, hcard, hk, hg, hgi⟩ := pa450010_rec (b := false) (by norm_num)
    pa450010_J_hd pa450010_J_sl
  have hk2 : pa450010J.k = 2 := hk
  rw [hk2] at hg hgi
  exact ⟨x, hx, hN, hmem, hcard, hk2, hg, hgi⟩

@[expose] noncomputable def pa450010j (i : ℕ) : Perm (Fin 28) := pa450010wv false 2 pa450010wJ[i]!

theorem pa450010_j_mem {i : ℕ} (hi : i < 2) : pa450010j i ∈ pa450010Jg :=
  pa450010_gen_mem false 2 pa450010wJ hi

theorem pa450010_Jg_eq : pa450010Jg = closure (pa450010j '' {j | j < 2}) := rfl

theorem pa450010_J_le_E : pa450010Jg ≤ D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) := by
  obtain ⟨-, -, -, -, -, -, hg, -⟩ := pa450010_J_rec
  exact le_inf ((closure_le _).2 (by rintro _ ⟨j, -, rfl⟩; exact pa450010wv_memD false _))
    (pa450010_cl_le_cent rfl hg pa450010_J_cent)

theorem pa450010_le_normalizer {G : Type*} [Group G] {S T : Set G} [Finite (closure T)]
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ closure T) :
    closure S ≤ normalizer ((closure T : Subgroup G) : Set G) := by
  rw [closure_le]
  intro s hs
  have hle : (closure T).map (MulAut.conj s).toMonoidHom ≤ closure T := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact h s hs t ht
  have heq : (closure T).map (MulAut.conj s).toMonoidHom = closure T :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective])
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact hle ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', e⟩ := hg
    have e' : g' = g := by simpa using e
    exact e' ▸ hg'

theorem pa450010_E_le_norm :
    D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) ≤
      normalizer (pa450010Jg : Set (Perm (Fin 28))) := by
  obtain ⟨xJ, hxJ, -, hmem, -, -, hgJ, -⟩ := pa450010_J_rec
  obtain ⟨-, -, -, -, -, hk, hg, hgi⟩ := pa450010_rec (b := false) (by norm_num) pa450010_CDX_hd
    pa450010_CDX_sl
  have hk4 : pa450010CDX.k = 4 := hk
  rw [hk4] at hg hgi
  have hc := conjInK_spec (by norm_num) hxJ hmem hg hgi hgJ pa450010_EJ
  rw [pa450010_E_eq]
  refine pa450010_le_normalizer ?_
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  exact hc i hi j hj

theorem pa450010_comm_of {a b z : Perm (Fin 28)} (h : a * b = z * b * a) : ⁅a, b⁆ = z := by
  rw [commutatorElement_def, h]
  group

theorem pa450010_comm_mem {cnt Z : ℕ} {T P P' : ℕ → ℕ} {x : ℕ → Perm (Fin 28)}
    {H : Subgroup (Perm (Fin 28))} {z : Perm (Fin 28)} (hx : ∀ q < cnt, PRep 28 5 (T q) (x q))
    (hH : ∀ y, y ∈ H ↔ ∃ q < cnt, x q = y) (hz : PRep 28 5 Z z)
    (h : commToK 28 5 (mask 5) cnt T P cnt T P' Z = true) : z ∈ ⁅H, H⁆ := by
  obtain ⟨p, hp, q, hq, e⟩ := commToK_spec (by norm_num) hx hx hz h
  rw [← pa450010_comm_of e]
  exact commutator_mem_commutator ((hH _).2 ⟨p, hp, rfl⟩) ((hH _).2 ⟨q, hq, rfl⟩)

theorem pa450010_jOf_eq : jOf D28 pa450010x = pa450010Jg := by
  obtain ⟨xJ, hxJ, -, hmem, -, -, hgJ, -⟩ := pa450010_J_rec
  obtain ⟨xE, hxE, -, hmemE, -, hk, hg, hgi⟩ := pa450010_rec (b := false) (by norm_num)
    pa450010_CDX_hd pa450010_CDX_sl
  have hk4 : pa450010CDX.k = 4 := hk
  rw [hk4] at hg hgi
  have hEn := pa450010_E_le_norm
  have hJE := pa450010_J_le_E
  change ⁅D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))),
    D28 ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))⁆ = pa450010Jg
  rw [pa450010_E_eq] at hEn hJE ⊢
  apply le_antisymm
  · have hcomm := commInK_spec (by norm_num) hxJ hmem hg hgi pa450010_EE
    refine CFSG.ClassicalGroups.Orthogonal.commutator_le_of_le_closure
      (S := (fun j => pa450010wv false 2 pa450010wCDX[j]!) '' {j | j < pa450010wCDX.length})
      (fun g hg' y hy => (mem_normalizer_iff.1 (hEn hg') y).1 hy) hJE subset_closure
      (closure_mono Set.subset_union_left) ?_
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    rw [commutatorElement_def]
    exact hcomm i hi j hj
  · rw [pa450010_Jg_eq, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · exact pa450010_comm_mem hxE hmemE (hgJ 0 (by norm_num)) pa450010_AB1
    · exact pa450010_comm_mem hxE hmemE (hgJ 1 (by norm_num)) pa450010_AB2

theorem pa450010_card_J : Nat.card ↥(jOf D28 pa450010x) = 60 := by
  rw [pa450010_jOf_eq]
  exact pa450010_J_rec.choose_spec.2.2.2.1

theorem pa450010_J_perf : ⁅pa450010Jg, pa450010Jg⁆ = pa450010Jg := by
  obtain ⟨xJ, hxJ, -, hmem, -, -, hgJ, -⟩ := pa450010_J_rec
  refine le_antisymm (pa450010_comm_le_self _) ?_
  rw [pa450010_Jg_eq, closure_le, ← pa450010_Jg_eq]
  rintro _ ⟨j, hj, rfl⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact pa450010_comm_mem hxJ hmem (hgJ 0 (by norm_num)) pa450010_JP1
  · exact pa450010_comm_mem hxJ hmem (hgJ 1 (by norm_num)) pa450010_JP2

theorem pa450010_J_center : ∀ j ∈ jOf D28 pa450010x,
    (∀ j' ∈ jOf D28 pa450010x, j * j' = j' * j) → j = 1 := by
  obtain ⟨xJ, hxJ, -, hmem, -, -, hgJ, -⟩ := pa450010_J_rec
  rw [pa450010_jOf_eq]
  intro j hj hc
  obtain ⟨i, hi, rfl⟩ := (hmem j).1 hj
  exact centOneK_spec (by norm_num) (by norm_num) hxJ hgJ pa450010_Jcent i hi
    fun k hk => hc _ (pa450010_j_mem hk)

@[expose] noncomputable def pa450010Rg : Subgroup (Perm (Fin 28)) := pa450010cl false 4 pa450010wR

theorem pa450010_R_facts : ⁅pa450010Rg, pa450010Rg⁆ = pa450010Rg ∧ Nat.card pa450010Rg = 60 ∧
    pa450010Rg ≤ K28 false ⊓ centralizer ({pG false} : Set (Perm (Fin 28))) := by
  obtain ⟨xR, hxR, -, hmem, hcard, hk, hg, -⟩ := pa450010_rec (b := false) (by norm_num)
    pa450010_R_hd pa450010_R_sl
  have hk2 : pa450010R.k = 2 := hk
  rw [hk2] at hg
  have hrep4 := pa450010_root (b := false) (kS := 4) (by norm_num) pa450010_C14_root
  have e4 : pa450010wv false 4 (pa450010wReps.getD 4 []) = pG false := (pa450010_rep_eq false).2.2.1
  rw [e4] at hrep4
  refine ⟨le_antisymm (pa450010_comm_le_self _) ?_, hcard, le_inf ?_ ?_⟩
  · change Subgroup.closure _ ≤ _
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · exact pa450010_comm_mem hxR hmem (hg 0 (by norm_num)) pa450010_RP1
    · exact pa450010_comm_mem hxR hmem (hg 1 (by norm_num)) pa450010_RP2
  · exact (closure_le _).2 (by rintro _ ⟨j, -, rfl⟩; exact pa450010wv_mem false 4 _)
  · have h := closure_le_centralizer (by norm_num) hg hrep4 pa450010_R_cent
    exact h

end CertificateChecks.KernelPropA

end
