
module

public import Certificates.Kernel.LyBenes.Kit
public import Certificates.Kernel.LyBenes.RBA
public import Certificates.Kernel.LyBenes.RBB
public import CFSG.Certificates.Kernel.LyBenes.Sound
public import CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase
import all CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase

public section

namespace CertificateChecks.KernelLyB

open Equiv CFSG.KC CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.LyBenes CFSG.KC.MonsterConv.Perm
  CertificateChecks.KernelLy CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem bind_parts : bindOK CS (NS 0) = true ∧ bindOK DS (NS 1) = true := by
  have h := bind_ok
  unfold kitBindOK at h
  exact andB_eq h

theorem bind0 : bindOK CS (NS 0) = true := bind_parts.1

theorem bind1 : bindOK DS (NS 1) = true := bind_parts.2

theorem valid_all : ∀ i < 6, StagesValid 17 (NS i) := by
  have h := valid_ok
  unfold kitValidOK at h
  have h1 := andB_eq (andB_eq h).1
  have h2 := andB_eq (andB_eq h).2
  intro i hi
  interval_cases i
  · exact (bindOK_sound bind0).1
  · exact (bindOK_sound bind1).1
  · exact stagesValid_of_netValid h1.1
  · exact stagesValid_of_netValid h1.2
  · exact stagesValid_of_netValid h2.1
  · exact stagesValid_of_netValid h2.2

theorem valid_pair {i j : Nat} (hi : i < 6) (hj : j < 6) :
    ∀ N ∈ [NS i, NS j], StagesValid 17 N := by
  intro N hN
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl
  · exact valid_all i hi
  · exact valid_all j hj

theorem inv_all : ∀ i j, (i, j) ∈ [(0, 0), (2, 1), (3, 3), (4, 4), (5, 5)] →
    ∀ r < 2 ^ 17, compN 17 [NS i, NS j] r = r := by
  have h := inv_ok
  unfold kitInvOK at h
  have h1 := andB_eq (andB_eq h).1
  have h2 := andB_eq (andB_eq h).2
  have h3 := andB_eq h2.2
  intro i j hij
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact planesId_sound (valid_pair (by decide) (by decide)) h1.1
  · exact planesId_sound (valid_pair (by decide) (by decide)) h1.2
  · exact planesId_sound (valid_pair (by decide) (by decide)) h2.1
  · exact planesId_sound (valid_pair (by decide) (by decide)) h3.1
  · exact planesId_sound (valid_pair (by decide) (by decide)) h3.2

theorem deg_le : Ly0.deg ≤ 2 ^ 17 := by norm_num

theorem nrep_c (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat)) :
    NRep 17 Ly0.deg (NS 0) Ly0.cG := fun a => by
  rw [(bindOK_sound bind0).2 a a.2]
  exact hc a

theorem nrep_d (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) :
    NRep 17 Ly0.deg (NS 1) Ly0.dG := fun a => by
  rw [(bindOK_sound bind1).2 a a.2]
  exact hd a

theorem zIdx_lt (z : Int) (hz : z ≠ 0 ∧ z.natAbs ≤ 2) : zIdx z < 6 := by
  have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem nrep_z (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (z : Int) (hz : z ≠ 0 ∧ z.natAbs ≤ 2) :
    NRep 17 Ly0.deg (NS (zIdx z)) (Ly0.letterG Ly0.gens0 z) := by
  have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · have e : Ly0.letterG Ly0.gens0 1 = Ly0.cG := by
      simp [Ly0.letterG_pos, Ly0.gens0_zero]
    rw [e]
    exact nrep_c hc
  · have e : Ly0.letterG Ly0.gens0 (-1) = Ly0.cG⁻¹ := by
      simp [Ly0.letterG_neg_of, Ly0.gens0_zero]
    rw [e]
    exact (nrep_c hc).inv deg_le (inv_all 0 0 (by decide))
  · have e : Ly0.letterG Ly0.gens0 2 = Ly0.dG := by
      simp [Ly0.letterG_pos, Ly0.gens0_one]
    rw [e]
    exact nrep_d hd
  · have e : Ly0.letterG Ly0.gens0 (-2) = Ly0.dG⁻¹ := by
      simp [Ly0.letterG_neg_of, Ly0.gens0_one]
    rw [e]
    exact (nrep_d hd).inv deg_le (inv_all 2 1 (by decide))

theorem wG_eq_prod (gs : ℕ → Perm (Fin Ly0.deg)) :
    ∀ w : List ℤ, Ly0.wG gs w = (w.map (Ly0.letterG gs)).prod
  | [] => by simp
  | l :: w => by simp [wG_eq_prod gs w]

theorem nrep_gen (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) {i : Fin 6} {j : Nat} (hj : j < 6)
    (hg : planesEq 17 (genNets NS (genZ i)) (NS j) = true) : NRep 17 Ly0.deg (NS j) (gB i) := by
  have hv : ∀ M ∈ genNets NS (genZ i), StagesValid 17 M := by
    intro M hM
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hM
    exact valid_all _ (zIdx_lt z (genZ_mem i z hz))
  have e := planesEq_sound hv (valid_all j hj) hg
  intro a
  rw [← e a (lt_of_lt_of_le a.2 deg_le)]
  have e2 : genNets NS (genZ i) = (genZ i).map fun z => NS (zIdx z) := rfl
  have e3 : gB i = Ly0.wG Ly0.gens0 (genZ i) := by simp [gB]
  rw [e2, compN_map _ _ (genZ i) (fun z hz => nrep_z hc hd z (genZ_mem i z hz)) a, e3,
    wG_eq_prod]

theorem gen_parts :
    planesEq 17 (genNets NS (genZ 2)) (NS 3) = true ∧ planesEq 17 (genNets NS (genZ 3)) (NS 4) = true ∧
      planesEq 17 (genNets NS (genZ 4)) (NS 5) = true := by
  have h := gen_ok
  unfold kitGenOK at h
  exact ⟨(andB_eq h).1, andB_eq (andB_eq h).2⟩

theorem nrep_letter (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (l : Fin 6 × Bool) (hl : l.1.val < 5) :
    NRep 17 Ly0.deg (NS (letIdx l)) (if l.2 then gB l.1 else (gB l.1)⁻¹) := by
  have g0 : gB 0 = Ly0.cG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]
  have g1 : gB 1 = Ly0.dG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]
  obtain ⟨⟨i, hi⟩, s⟩ := l
  change i < 5 at hl
  interval_cases i <;> cases s
  · change NRep 17 Ly0.deg (NS 0) (gB 0)⁻¹
    rw [g0]
    exact (nrep_c hc).inv deg_le (inv_all 0 0 (by decide))
  · change NRep 17 Ly0.deg (NS 0) (gB 0)
    rw [g0]
    exact nrep_c hc
  · change NRep 17 Ly0.deg (NS 2) (gB 1)⁻¹
    rw [g1]
    exact (nrep_d hd).inv deg_le (inv_all 2 1 (by decide))
  · change NRep 17 Ly0.deg (NS 1) (gB 1)
    rw [g1]
    exact nrep_d hd
  · change NRep 17 Ly0.deg (NS 3) (gB 2)⁻¹
    exact (nrep_gen hc hd (by decide) gen_parts.1).inv deg_le (inv_all 3 3 (by decide))
  · change NRep 17 Ly0.deg (NS 3) (gB 2)
    exact nrep_gen hc hd (by decide) gen_parts.1
  · change NRep 17 Ly0.deg (NS 4) (gB 3)⁻¹
    exact (nrep_gen hc hd (by decide) gen_parts.2.1).inv deg_le (inv_all 4 4 (by decide))
  · change NRep 17 Ly0.deg (NS 4) (gB 3)
    exact nrep_gen hc hd (by decide) gen_parts.2.1
  · change NRep 17 Ly0.deg (NS 5) (gB 4)⁻¹
    exact (nrep_gen hc hd (by decide) gen_parts.2.2).inv deg_le (inv_all 5 5 (by decide))
  · change NRep 17 Ly0.deg (NS 5) (gB 4)
    exact nrep_gen hc hd (by decide) gen_parts.2.2

theorem letIdx_lt (l : Fin 6 × Bool) (hl : l.1.val < 5) : letIdx l < 6 := by
  obtain ⟨⟨i, hi⟩, s⟩ := l
  change i < 5 at hl
  interval_cases i <;> cases s <;> decide +revert

theorem lift_mk_eq_prod {G : Type*} [Group G] (g : Fin 6 → G) :
    ∀ r : List (Fin 6 × Bool),
      FreeGroup.lift g (FreeGroup.mk r) = (r.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod
  | [] => by rw [← FreeGroup.one_eq_mk, map_one, List.map_nil, List.prod_nil]
  | l :: r => by
    have e : FreeGroup.mk (l :: r) = FreeGroup.mk [l] * FreeGroup.mk r := rfl
    rw [e, map_mul, lift_mk_single, lift_mk_eq_prod g r, List.map_cons, List.prod_cons]

theorem lift_gB_of_bNetOK (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) {r : List (Fin 6 × Bool)}
    (h : bNetOK NS r = true) : FreeGroup.lift gB (FreeGroup.mk r) = 1 := by
  have h' := h
  unfold bNetOK at h'
  obtain ⟨hb, hp⟩ := andB_eq h'
  have hl : ∀ l ∈ r, l.1.val < 5 := by
    intro l hl
    unfold isBWord at hb
    exact of_decide_eq_true (List.all_eq_true.1 hb l hl)
  have hv : ∀ N ∈ wordNets NS r, StagesValid 17 N := by
    intro N hN
    obtain ⟨l, hlr, rfl⟩ := List.mem_map.1 hN
    exact valid_all _ (letIdx_lt l (hl l hlr))
  rw [lift_mk_eq_prod]
  exact prod_eq_one deg_le (fun l => NS (letIdx l)) _ r
    (fun l hlr => nrep_letter hc hd l (hl l hlr)) (planesId_sound hv hp)

theorem all_of_chunks {α : Type*} (p : α → Bool) (s : Nat) :
    ∀ (m : Nat) (L : List α), L.length ≤ s * m →
      (∀ j < m, ((L.drop (s * j)).take s).all p = true) → L.all p = true
  | 0, L, hm, _ => by
    have hL : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hL]
    rfl
  | m + 1, L, hm, h => by
    have h0 := h 0 (by omega)
    rw [Nat.mul_zero, List.drop_zero] at h0
    have ih := all_of_chunks p s m (L.drop s) (by rw [List.length_drop]; rw [Nat.mul_succ] at hm; omega)
      (fun j hj => by
        have h1 := h (j + 1) (by omega)
        have e : (L.drop s).drop (s * j) = L.drop (s * (j + 1)) := by
          rw [List.drop_drop]
          congr 1
          ring
        rw [e]
        exact h1)
    rw [← List.take_append_drop s L, List.all_append, h0, ih, Bool.and_self]

theorem rb_all : RB.all (bNetOK NS) = true := by
  refine all_of_chunks _ 8 12 _ (by decide +kernel) fun j hj => ?_
  interval_cases j
  exacts [rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11]

end CertificateChecks.KernelLyB

end
