module

public import CFSG.Certificates.Kernel.G23F48.ConjCount
public import Certificates.Kernel.G23F48.A22Glue

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)
open MulAction

theorem coverP_mem {T : List (ℕ × ℕ × ℕ)} {lo m q : ℕ} (h : coverP T lo m = true) (hq : q < m) :
    lo + q ∈ T.map Prod.fst := by
  unfold coverP at h
  rw [List.all_eq_true] at h
  exact List.contains_iff_mem.1 (h q (List.mem_range.2 hq))

theorem mem_tree {T : List (ℕ × ℕ × ℕ)} {x : ℕ} (h : x ∈ T.map Prod.fst) :
    ∃ i < T.length, (T.getD i (0, 0, 0)).1 = x := by
  obtain ⟨⟨a, b⟩, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
  refine ⟨i, hi, ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]

theorem eq_of_orbit364 {R X P : Subgroup (Equiv.Perm (Fin 728))} {pt : Fin 728}
    (O : Finset (Fin 728)) (hO : O.card = 364) (hOR : ∀ r ∈ O, ∃ g ∈ R, g pt = r) (hPR : P ≤ R)
    (hPpt : P ≤ stabilizer (Equiv.Perm (Fin 728)) pt) (hc : Nat.card X = 364 * Nat.card P)
    (hRX : R ≤ X) : R = X := by
  have h1 := CFSG.Certificates.card_mul_card_inf_stabilizer_le R pt O hOR
  have h2 := Subgroup.card_le_of_le (le_inf hPR hPpt)
  rw [hO] at h1
  refine Subgroup.eq_of_le_of_card_ge hRX ?_
  rw [hc]
  exact (Nat.mul_le_mul_left 364 h2).trans h1

theorem mem_of_fix {X P R : Subgroup (Equiv.Perm (Fin 728))} {pt : Fin 728}
    (hP : P = X ⊓ stabilizer (Equiv.Perm (Fin 728)) pt) (hPR : P ≤ R) {g q h : Equiv.Perm (Fin 728)}
    (hgR : g ∈ R) (hgX : g ∈ X) (hq : q ∈ P) (hhX : h ∈ X) (he : q (h pt) = g pt) : h ∈ R := by
  have hqX : q ∈ X := by
    rw [hP] at hq
    exact hq.1
  have hu : h⁻¹ * q⁻¹ * g ∈ P := by
    rw [hP]
    refine ⟨X.mul_mem (X.mul_mem (X.inv_mem hhX) (X.inv_mem hqX)) hgX, mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def]
    simp only [Equiv.Perm.mul_apply]
    rw [← he]
    simp
  have e : h = q⁻¹ * g * (h⁻¹ * q⁻¹ * g)⁻¹ := by group
  rw [e]
  exact R.mul_mem (R.mul_mem (R.inv_mem (hPR hq)) hgR) (R.inv_mem (hPR hu))

theorem gens_size : (burnsideF48t_g23Gens ()).size = 4 := rfl

theorem X_eq : arrGen 728 (burnsideF48t_g23Gens ()) =
    Subgroup.closure (Set.range fun k : Fin (burnsideF48t_g23Gens ()).size => gam k) :=
  CFSG.Sporadic.HNOddCore.arrGen_eq fun k hk => (prep_gen (gens_size ▸ hk)).1

theorem X_lt {g : Equiv.Perm (Fin 728)} (hg : g ∈ arrGen 728 (burnsideF48t_g23Gens ()))
    {x : Fin 728} (hx : (x : ℕ) < 364) : ((g x : Fin 728) : ℕ) < 364 := by
  rw [X_eq] at hg
  refine burnsideF48t_preserves (fun k hk => (prep_gen (gens_size ▸ hk)).1)
    (S := {x | (x : ℕ) < 364}) ?_ g hg x hx
  intro s hs y hy
  have hs4 : s < 4 := gens_size ▸ hs
  have h := allN_spec (allN_spec x_pres s hs4) y hy
  rw [Nat.blt_eq] at h
  rw [Set.mem_setOf_eq, ← (prep_gen hs4).2.1 y]
  exact h

theorem X_ge {g : Equiv.Perm (Fin 728)} (hg : g ∈ arrGen 728 (burnsideF48t_g23Gens ()))
    {x : Fin 728} (hx : 364 ≤ (x : ℕ)) : 364 ≤ ((g x : Fin 728) : ℕ) := by
  by_contra h
  have := X_lt (Subgroup.inv_mem _ hg) (not_le.1 h)
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at this
  omega

theorem gam_rep : ∀ s < 4, CFSG.ONSchreier.PRep 728 (burnsideF48t_g23Gens ())[s]! (gam s) ∧
    gam s ∈ arrGen 728 (burnsideF48t_g23Gens ()) := fun s hs => ⟨(prep_gen hs).1, gam_mem hs⟩

theorem p1_rep : ∀ s < 3, CFSG.ONSchreier.PRep 728 burnsideF48t_g23P1Arr[s]! (sig s) ∧
    sig s ∈ arrGen 728 burnsideF48t_g23P1Arr := fun s hs => by
  interval_cases s
  · exact ⟨(prep_letter (i := 0) (by norm_num)).1, sig_mem_arrGen (k := 0) (by decide) rfl
      (by norm_num)⟩
  · exact ⟨(prep_letter (i := 1) (by norm_num)).1, sig_mem_arrGen (k := 1) (by decide) rfl
      (by norm_num)⟩
  · exact ⟨(prep_letter (i := 2) (by norm_num)).1, sig_mem_arrGen (k := 2) (by decide) rfl
      (by norm_num)⟩

theorem P1_eq (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    arrGen 728 burnsideF48t_g23P1Arr =
      arrGen 728 (burnsideF48t_g23Gens ()) ⊓ stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) := by
  refine Subgroup.eq_of_le_of_card_ge P1_le ?_
  obtain ⟨Op, hOp, hOpX⟩ := orbit_X_0 gam_rep
  have h := CFSG.Certificates.card_mul_card_inf_stabilizer_le _ (0 : Fin 728) Op hOpX
  rw [hOp, hX] at h
  rw [(card_P1_P2_B hX).1]
  omega

theorem P2_eq (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    arrGen 728 burnsideF48t_g23P2Arr =
      arrGen 728 (burnsideF48t_g23Gens ()) ⊓ stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) := by
  refine Subgroup.eq_of_le_of_card_ge P2_le ?_
  obtain ⟨Oq, hOq, hOqX⟩ := orbit_X_364 gam_rep
  have h := CFSG.Certificates.card_mul_card_inf_stabilizer_le _ (364 : Fin 728) Oq hOqX
  rw [hOq, hX] at h
  rw [(card_P1_P2_B hX).2.1]
  omega

theorem B_eq (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    arrGen 728 burnsideF48t_g23BArr =
      arrGen 728 burnsideF48t_g23P1Arr ⊓ arrGen 728 burnsideF48t_g23P2Arr := by
  refine Subgroup.eq_of_le_of_card_ge
    (le_inf (B_le_P1.trans inf_le_left) (B_le_P2.trans inf_le_left)) ?_
  obtain ⟨O₁, hO₁, hO₁P⟩ := orbit_P1 p1_rep
  have h := CFSG.Certificates.card_mul_card_inf_stabilizer_le _ (364 : Fin 728) O₁ hO₁P
  have hinf : arrGen 728 burnsideF48t_g23P1Arr ⊓ arrGen 728 burnsideF48t_g23P2Arr =
      arrGen 728 burnsideF48t_g23P1Arr ⊓ stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) := by
    rw [P2_eq hX, ← inf_assoc, inf_eq_left.2 (P1_le.trans inf_le_left)]
  rw [hinf, (card_P1_P2_B hX).2.2]
  rw [hO₁, (card_P1_P2_B hX).1] at h
  omega

theorem ev_gam (ws : List (Fin 4 × Bool)) :
    Orb.PRep 728 10 (evP 728 10 GP GPI ws) (burnsideF48s_ev (fun i : Fin 4 => gam i) ws) ∧
      burnsideF48s_ev (fun i : Fin 4 => gam i) ws ∈ arrGen 728 (burnsideF48t_g23Gens ()) :=
  ⟨prep_evP (by norm_num) (by norm_num) (fun i => (prep_gen i.2).2) ws,
    burnsideF48s_ev_mem _ _ fun l _ => gam_mem l.1.2⟩

@[expose] noncomputable def s0g (j : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 (burnsideF48t_g23S0Arr ())[j]!

theorem prep_s0g {j : ℕ} (hj : j < 3) :
    CFSG.ONSchreier.PRep 728 (burnsideF48t_g23S0Arr ())[j]! (s0g j) ∧
      Orb.PRep 728 10 (S0C.S j) (s0g j) ∧ Orb.PRep 728 10 (S0C.SI j) (s0g j)⁻¹ := by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm (allN_spec s0_perm j (by omega))
  have ht : CFSG.ONSchreier.PRep 728 (burnsideF48t_g23S0Arr ())[j]! g := fun x => by
    rw [s0Arr_get.2 j hj, Orb.unpack_get x.2]
    exact hg x
  rw [s0g, onPermOfArr_eq ht]
  exact ⟨ht, hg, hgi⟩

theorem s0g_mem {j : ℕ} (hj : j < 3) : s0g j ∈ arrGen 728 (burnsideF48t_g23S0Arr ()) :=
  Subgroup.subset_closure ⟨j, by rw [s0Arr_get.1]; exact hj,
    CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_s0g hj).1⟩

theorem wS_letters : (wS.all fun w => w.all fun l => Nat.blt l.1 3) = true := by
  decide +kernel

theorem wS_lt {i : ℕ} : ∀ l ∈ wS.getD i [], l.1 < 3 := by
  intro l hl
  have h := List.all_eq_true.1 wS_letters
  by_cases hi : i < wS.length
  · rw [List.getD_eq_getElem _ _ hi] at hl
    have := List.all_eq_true.1 (h _ (List.getElem_mem hi)) l hl
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    simp at hl

theorem B_le_normalizer : arrGen 728 burnsideF48t_g23BArr ≤
    Subgroup.normalizer (arrGen 728 (burnsideF48t_g23S0Arr ()) : Set (Equiv.Perm (Fin 728))) := by
  have hS : arrGen 728 (burnsideF48t_g23S0Arr ()) =
      Subgroup.closure (Set.range fun k : Fin (burnsideF48t_g23S0Arr ()).size => s0g k) :=
    CFSG.Sporadic.HNOddCore.arrGen_eq fun k hk => (prep_s0g (by rw [s0Arr_get.1] at hk; exact hk)).1
  have hconj : ∀ i < 2, ∀ j < 3,
      sig i * s0g j * (sig i)⁻¹ ∈ arrGen 728 (burnsideF48t_g23S0Arr ()) := by
    intro i hi j hj
    have hw := prep_evPN (k := 3) (σ := s0g) (by norm_num) (by norm_num)
      (fun t ht => (prep_s0g ht).2) (wS.getD (3 * i + j) []) wS_lt
    rw [Nat.eq_of_beq_eq_true (allN_spec (allN_spec s0_norm i hi) j hj)] at hw
    have hc : Orb.PRep 728 10 (pconj 728 10 (LP i) (LPI i) (S0C.S j)) (sig i * s0g j * (sig i)⁻¹) :=
      Orb.prep_pcomp (by norm_num) (Orb.prep_pcomp (by norm_num) (prep_letter (by omega)).2.1
        (prep_s0g hj).2.1) (prep_letter (by omega)).2.2
    rw [oprep_unique hc hw]
    exact wv_mem (fun t ht => s0g_mem ht) _ wS_lt
  have hnorm : ∀ k < 2, sig k ∈
      Subgroup.normalizer (arrGen 728 (burnsideF48t_g23S0Arr ()) : Set (Equiv.Perm (Fin 728))) := by
    intro k hk2
    refine mem_normalizer_of_conj fun x hx => ?_
    have hle : arrGen 728 (burnsideF48t_g23S0Arr ()) ≤
        (arrGen 728 (burnsideF48t_g23S0Arr ())).comap (MulAut.conj (sig k)).toMonoidHom := by
      refine (le_of_eq hS).trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      have hj3 : j < 3 := by
        rw [s0Arr_get.1] at hj
        exact hj
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact hconj k hk2 j hj3
    exact hle hx
  refine arrGen_letters_le id fun k hk => ?_
  have hk2 : k < 2 := hk
  interval_cases k
  · exact ⟨by norm_num, rfl, hnorm 0 (by norm_num)⟩
  · exact ⟨by norm_num, rfl, hnorm 1 (by norm_num)⟩

end CFSG.KC.G23F48

end
