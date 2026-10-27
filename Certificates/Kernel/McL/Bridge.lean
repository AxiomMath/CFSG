module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.McL.G1
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.McL.RelatorsB

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CFSG.Certificates.McLD TauCeti
open CertificateChecks.KernelHe CertificateChecks.KernelRu

theorem ival_hom {H K : Type*} [Group H] [Group K] (f : H →* K) (g : ℕ → H) (W n : ℕ) :
    f (ival g W n) = ival (fun c => f (g c)) W n := by
  unfold ival
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem ival_congr {H : Type*} [Group H] (g h : ℕ → H) {W n : ℕ}
    (hl : ∀ i < n, wLet W i < 4) (e : ∀ c < 4, g c = h c) : ival g W n = ival h W n := by
  unfold ival
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [e _ (hl i (List.mem_range.mp hi))]

theorem lift_fgx {K : Type*} [Group K] (y : ℕ → K) {W n : ℕ} (h : ∀ i < n, wLet W i < 6) :
    FreeGroup.lift (fun i : Fin 4 => y i.val) (fword fgx W n) = bval y W n := by
  rw [hom_fword]
  unfold bval
  congr 1
  apply List.map_congr_left
  intro i hi
  have hl := h i (List.mem_range.mp hi)
  have e : wLet W i / 2 % 4 = wLet W i / 2 := by omega
  unfold letV fgx
  split_ifs <;> first | omega | simp [e]

theorem lift_fgc {K : Type*} [Group K] (y : ℕ → K) {W n : ℕ} (h : ∀ i < n, wLet W i < 4) :
    FreeGroup.lift (fun i : Fin 4 => y i.val) (fword fgc W n) = ival y W n := by
  rw [hom_fword]
  unfold ival
  congr 1
  apply List.map_congr_left
  intro i hi
  have hl := h i (List.mem_range.mp hi)
  have e : wLet W i % 4 = wLet W i := by omega
  split_ifs <;> first | omega | simp [fgc, e]

theorem th_andB_iff (a b : Bool) : Th.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [Th.andB]

theorem memb_sound {H : Type*} [Group H] (z : ℕ → H) {e c : ℕ}
    (hm : McL.Dce.membWordOK e c = true) (hlet : ∀ i < LceS.wLen e, wLet (LceS.wWord e) i < 4)
    (h1 : ival z (LceS.wWord e) (LceS.wLen e) = 1) :
    z c ∈ Subgroup.closure (z '' {j | j < 4 ∧ j ≠ c}) := by
  dsimp only [McL.Dce.membWordOK] at hm
  rw [th_andB_iff, th_andB_iff] at hm
  obtain ⟨hn, h0, hr⟩ := hm
  have hn' : 0 < LceS.wLen e := by
    rw [← Nat.blt_eq]
    exact hn
  have h0' : wLet (LceS.wWord e) 0 = c := Nat.eq_of_beq_eq_true h0
  have hr' := rec_acc_sound
    (fun i => McL.Dce.notB (Nat.beq (McL.Dce.byte (Nat.shiftRight e 12) (Nat.succ i)) c)) hr
  obtain ⟨m, hlen⟩ : ∃ m, LceS.wLen e = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn').symm⟩
  have hc4 : c < 4 := by
    have h := hlet 0 hn'
    rwa [h0'] at h
  have hv := h1
  unfold ival at hv
  rw [hlen, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, h0'] at hv
  split_ifs at hv with h255
  · omega
  rw [eq_inv_of_mul_eq_one_left hv]
  apply Subgroup.inv_mem
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < m := List.mem_range.mp hi
  have hl := hlet (i + 1) (by omega)
  have hne : wLet (LceS.wWord e) (i + 1) ≠ c := by
    intro heq
    have hx := hr' i (by
      change i < LceS.wLen e - 1
      omega)
    change McL.Dce.notB (Nat.beq (wLet (LceS.wWord e) (i + 1)) c) = true at hx
    rw [heq, Nat.beq_refl] at hx
    exact absurd hx (by decide)
  simp only [Function.comp_apply]
  split_ifs with h
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨_, ⟨hl, hne⟩, rfl⟩

theorem rels1_hold : ∀ r ∈ rels1, FreeGroup.lift (fun i : Fin 4 => yv gP i.val) r = 1 := by
  intro r hr
  unfold rels1 at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · rw [lift_fgx _ (nr1_letters k hk)]
    exact relsP.1 k hk
  · rw [lift_fgc _ (gr_letters k hk)]
    exact relsP.2 k hk

noncomputable def φ1 : G1 →* Sporadic.mclPresentation.Group := PresentedGroup.toGroup rels1_hold

theorem φ1_gen1 : ∀ c < 4, φ1 (gen1 c) = yv gP c := by
  intro c hc
  unfold gen1 φ1
  rw [PresentedGroup.toGroup.of]
  congr 1
  exact Nat.mod_eq_of_lt hc

theorem gens_eq : Sporadic.mclPresentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount, Sporadic.mclPresentation_generatorNames]

theorem b_pow5 : gP 1 ^ 5 = 1 := by
  have h := (tc_ok 1 (by norm_num)).2
  rw [bval_eq_list _ _ _ [2, 2, 2, 2, 2] (by decide)] at h
  simpa [letV, pow_succ, mul_assoc] using h

theorem ab_pow11 : (gP 0 * gP 1) ^ 11 = 1 := by
  have h := (tc_ok 3 (by norm_num)).2
  rw [bval_eq_list _ _ _ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
    (by decide)] at h
  simpa [letV, pow_succ, mul_assoc] using h

theorem le_of_ab {L : Subgroup Sporadic.mclPresentation.Group} (ha : gP 0 ∈ L) (hb : gP 1 ∈ L) :
    L = ⊤ := by
  rw [eq_top_iff, ← KB.closure_tcGen Sporadic.mclPresentation, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g < 2 := by
    rw [← gens_eq]
    exact hg
  interval_cases g
  · exact ha
  · exact hb

theorem φ1_surjective : Function.Surjective φ1 := by
  obtain ⟨y0, y1, y2, y3⟩ := yv_eq gP
  set H := Subgroup.closure (yv gP '' {j | j < 4}) with hH
  have hmem : ∀ j < 4, yv gP j ∈ H := fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩
  have htr : ival (yv gP) (LceS.wWord (trw 1)) (LceS.wLen (trw 1)) = 1 := by
    have hl := entsBelow_sound let_TRW 1 (by norm_num)
    calc ival (yv gP) (LceS.wWord (trw 1)) (LceS.wLen (trw 1))
        = ival (fun c => φ1 (gen1 c)) (LceS.wWord (trw 1)) (LceS.wLen (trw 1)) :=
          (ival_congr _ _ hl φ1_gen1).symm
      _ = φ1 (ival gen1 (LceS.wWord (trw 1)) (LceS.wLen (trw 1))) := (ival_hom _ _ _ _).symm
      _ = 1 := by rw [g1_traces 1 (by norm_num), map_one]
  have hx3 := memb_sound (yv gP) (e := trw 1) CFSG.KD.McL.Bind.trw1
    (entsBelow_sound let_TRW 1 (by norm_num)) htr
  have hK : Subgroup.closure (yv gP '' {j | j < 4 ∧ j ≠ 2}) ≤
      H.comap (MulAut.conj (gP 1)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, ⟨hj4, hj2⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    interval_cases j
    · have e : gP 1 * yv gP 0 * (gP 1)⁻¹ = yv gP 3 := by rw [y0, y3]
      rw [e]
      exact hmem 3 (by norm_num)
    · have e : gP 1 * yv gP 1 * (gP 1)⁻¹ = yv gP 0 := by
        rw [y0, y1]
        group
      rw [e]
      exact hmem 0 (by norm_num)
    · exact absurd rfl hj2
    · have e : gP 1 * yv gP 3 * (gP 1)⁻¹ = yv gP 2 := by
        rw [y2, y3]
        group
      rw [e]
      exact hmem 2 (by norm_num)
  have hHK : H ≤ Subgroup.closure (yv gP '' {j | j < 4 ∧ j ≠ 2}) := by
    rw [hH, Subgroup.closure_le]
    rintro _ ⟨j, hj4, rfl⟩
    by_cases hj : j = 2
    · subst hj
      exact hx3
    · exact Subgroup.subset_closure ⟨j, ⟨hj4, hj⟩, rfl⟩
  have hconj : ∀ x ∈ H, gP 1 * x * (gP 1)⁻¹ ∈ H := by
    intro x hx
    have h := hK (hHK hx)
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  have hconjk : ∀ k : ℕ, ∀ x ∈ H, gP 1 ^ k * x * (gP 1 ^ k)⁻¹ ∈ H := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro x hx
      have e : gP 1 ^ (k + 1) * x * (gP 1 ^ (k + 1))⁻¹ =
          gP 1 ^ k * (gP 1 * x * (gP 1)⁻¹) * (gP 1 ^ k)⁻¹ := by
        rw [pow_succ]
        group
      rw [e]
      exact ih _ (hconj x hx)
  have ha : gP 0 ∈ H := by
    rw [← y0]
    exact hmem 0 (by norm_num)
  have habk : ∀ k : ℕ, (gP 0 * gP 1) ^ k * (gP 1 ^ k)⁻¹ ∈ H := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (gP 0 * gP 1) ^ (k + 1) * (gP 1 ^ (k + 1))⁻¹ =
          (gP 0 * gP 1) ^ k * (gP 1 ^ k)⁻¹ * (gP 1 ^ k * gP 0 * (gP 1 ^ k)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact H.mul_mem ih (hconjk k _ ha)
  have hb : gP 1 ∈ H := by
    have h := habk 11
    rw [ab_pow11, one_mul] at h
    have e : gP 1 = (gP 1 ^ 11)⁻¹⁻¹ := by
      rw [inv_inv]
      have e' : gP 1 ^ 11 = (gP 1 ^ 5) ^ 2 * gP 1 := by group
      rw [e', b_pow5, one_pow, one_mul]
    rw [e]
    exact H.inv_mem h
  have htop : H = ⊤ := le_of_ab ha hb
  rw [hH] at htop
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨gen1 j, φ1_gen1 j hj⟩

theorem evenLens_sound {REL : ℕ → ℕ} {N : ℕ} (h : McL.Sub.evenLens REL N = true) :
    ∀ r < N, LceS.wLen (REL r) % 2 = 0 := by
  induction N with
  | zero => exact fun r hr => absurd hr (Nat.not_lt_zero r)
  | succ n ih =>
    have hA : McL.Sub.evenLens REL n = true ∧
        Nat.beq (Nat.land (LceS.wLen (REL n)) 1) 0 = true := by
      revert h
      change Bool.rec (motive := fun _ => Bool) false
        (Nat.beq (Nat.land (LceS.wLen (REL n)) 1) 0) (McL.Sub.evenLens REL n) = true → _
      cases McL.Sub.evenLens REL n <;> cases Nat.beq (Nat.land (LceS.wLen (REL n)) 1) 0 <;> simp
    intro r hr
    rcases Nat.lt_or_ge r n with hn | hn
    · exact ih hA.1 r hn
    · have e : r = n := by omega
      subst e
      rw [← Nat.and_one_is_mod]
      exact Nat.eq_of_beq_eq_true hA.2

noncomputable def ε1 : G1 →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ => Multiplicative.ofAdd 1) (by
    have hw : ∀ (F : ℕ → FreeGroup (Fin 4)),
        (∀ l, FreeGroup.lift (fun _ : Fin 4 => Multiplicative.ofAdd (1 : ZMod 2)) (F l) =
          Multiplicative.ofAdd 1) →
        ∀ W n, n % 2 = 0 →
          FreeGroup.lift (fun _ : Fin 4 => Multiplicative.ofAdd (1 : ZMod 2)) (fword F W n) = 1 := by
      intro F hF W n hn
      rw [hom_fword, List.map_congr_left (g := fun _ => Multiplicative.ofAdd (1 : ZMod 2))
        (fun i _ => hF (wLet W i)), List.map_const', List.length_range, List.prod_replicate,
        ← ofAdd_nsmul, nsmul_one]
      have h0 : (n : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff n 2).mpr (Nat.dvd_of_mod_eq_zero hn)
      rw [h0]
      rfl
    have hpK := evenLens_sound CFSG.KD.McL.Bind.pK
    have hpG := evenLens_sound CFSG.KD.McL.Bind.pG
    intro r hr
    unfold rels1 at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · apply hw
      · intro l
        unfold fgx
        split_ifs
        · simp
        · rw [map_inv, FreeGroup.lift_apply_of]
          rfl
      · exact hpK k hk
    · apply hw
      · intro l
        simp [fgc]
      · exact hpG k hk)

theorem ε1_surjective : Function.Surjective ε1 := by
  intro v
  obtain ⟨x, rfl⟩ : ∃ x : ZMod 2, Multiplicative.ofAdd x = v := ⟨v.toAdd, rfl⟩
  fin_cases x
  · exact ⟨1, map_one _⟩
  · refine ⟨gen1 0, ?_⟩
    unfold gen1 ε1
    rw [PresentedGroup.toGroup.of]
    rfl

theorem mcl : Finite SporadicName.McL.Group ∧ Nat.card SporadicName.McL.Group ≤ 898128000 := by
  obtain ⟨hfin, hcard⟩ := g1_card
  have hidx : ε1.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr ε1_surjective, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
    simp
  have hsq : ∀ p : Sporadic.mclPresentation.Group, p ^ 2 ∈ ε1.ker.map φ1 := by
    intro p
    obtain ⟨x, rfl⟩ := φ1_surjective p
    exact ⟨x ^ 2, Subgroup.sq_mem_of_index_two hidx x, map_pow _ _ _⟩
  have hb : gP 1 ∈ ε1.ker.map φ1 := by
    have e : gP 1 = (gP 1 ^ 3) ^ 2 := by
      rw [← pow_mul]
      have e' : gP 1 ^ (3 * 2) = gP 1 ^ 5 * gP 1 := by
        rw [← pow_succ]
      rw [e', b_pow5, one_mul]
    rw [e]
    exact hsq _
  have hab : gP 0 * gP 1 ∈ ε1.ker.map φ1 := by
    have e : gP 0 * gP 1 = ((gP 0 * gP 1) ^ 6) ^ 2 := by
      rw [← pow_mul]
      have e' : (gP 0 * gP 1) ^ (6 * 2) = (gP 0 * gP 1) ^ 11 * (gP 0 * gP 1) := by
        rw [← pow_succ]
      rw [e', ab_pow11, one_mul]
    rw [e]
    exact hsq _
  have ha : gP 0 ∈ ε1.ker.map φ1 := by
    have e : gP 0 = gP 0 * gP 1 * (gP 1)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hab (Subgroup.inv_mem _ hb)
  have htop := le_of_ab ha hb
  have hsurj : Function.Surjective fun k : ε1.ker => φ1 k := by
    intro p
    have hp : p ∈ ε1.ker.map φ1 := by
      rw [htop]
      exact Subgroup.mem_top p
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨⟨k, hk⟩, rfl⟩
  have hK : Nat.card ε1.ker * 2 = Nat.card G1 := by
    have h := Subgroup.card_mul_index (H := ε1.ker)
    rwa [hidx] at h
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have hfinal : CFSG.KD.McL.D.NORD * CFSG.KD.McL.D.SUM / 2 = 898128000 :=
    Nat.eq_of_beq_eq_true CFSG.KD.McL.Bind.fin
  refine ⟨Finite.of_surjective (fun k : ε1.ker => φ1 k) hsurj, ?_⟩
  have h2 : Nat.card ε1.ker ≤ CFSG.KD.McL.D.NORD * CFSG.KD.McL.D.SUM / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), hK]
    exact hcard
  rw [hfinal] at h2
  exact hle.trans h2

end CertificateChecks.KernelMcL

end
