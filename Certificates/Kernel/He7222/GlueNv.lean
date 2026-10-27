module

public import Certificates.Kernel.He7222.GlueScan
public import Certificates.Kernel.He7222.NvK
public import Certificates.Kernel.He7222.NvTK
public import CFSG.Certificates.Kernel.He7222.NvSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725 CFSG.KS.PF

theorem comm_pow_mod {G : Type*} [Group G] {y τ : G} {p e : ℕ} (hp : Commute (y ^ p) τ)
    (he : y ^ e = 1) : Commute (y ^ (e % p)) τ := by
  have e1 : y ^ (e % p) = ((y ^ p) ^ (e / p))⁻¹ := by
    have := congrArg (fun k => y ^ k) (Nat.div_add_mod e p)
    rw [pow_add, pow_mul, he] at this
    exact eq_inv_of_mul_eq_one_right this
  rw [e1]
  exact (hp.pow_left _).inv_left

theorem conj_eq_of_commute {G : Type*} [Group G] {y τ : G} (h : Commute y τ) : y * τ * y⁻¹ = τ := by
  rw [h.eq, mul_inv_cancel_right]

theorem nv_false {G : Type*} [Group G] {τ s y : G} (hs2 : s * s = 1) (hts : τ * s = s * τ)
    (hyτ : y * τ * y⁻¹ = s) (hsτ : s ≠ τ) (hs1 : s ≠ 1)
    (hys : y * s * y⁻¹ = τ ∨ y * s * y⁻¹ = s ∨ y * s * y⁻¹ = τ * s ∨ y * s * y⁻¹ = 1)
    (he : ∃ e ∈ [25, 343, 17], y ^ e = 1) : False := by
  obtain ⟨e, hes, hye⟩ := he
  have h2 : y ^ 2 * τ * (y ^ 2)⁻¹ = y * s * y⁻¹ := by
    rw [← hyτ, sq]
    group
  have h1 : ∀ k, Commute (y ^ k) τ → k = 1 → False := fun k hk hk1 => by
    subst hk1
    rw [pow_one] at hk
    exact hsτ (by rw [← hyτ]; exact conj_eq_of_commute hk)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hys with hys | hys | hys | hys
  ·
    have hc : Commute (y ^ 2) τ := by
      change y ^ 2 * τ = τ * y ^ 2
      calc y ^ 2 * τ = y ^ 2 * τ * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = τ * y ^ 2 := by rw [h2, hys]
    have := comm_pow_mod hc hye
    rcases hes with rfl | rfl | rfl <;> exact h1 _ this (by norm_num)
  · exact hsτ (by
      calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
        _ = y⁻¹ * (y * τ * y⁻¹) * y := by rw [hys, hyτ]
        _ = τ := by group)
  ·
    have h3 : y ^ 3 * τ * (y ^ 3)⁻¹ = τ := by
      calc y ^ 3 * τ * (y ^ 3)⁻¹ = y * (y ^ 2 * τ * (y ^ 2)⁻¹) * y⁻¹ := by group
        _ = y * (τ * s) * y⁻¹ := by rw [h2, hys]
        _ = y * τ * y⁻¹ * (y * s * y⁻¹) := by group
        _ = s * (τ * s) := by rw [hyτ, hys]
        _ = τ * (s * s) := by rw [← mul_assoc, ← hts, mul_assoc]
        _ = τ := by rw [hs2, mul_one]
    have hc : Commute (y ^ 3) τ := by
      change y ^ 3 * τ = τ * y ^ 3
      calc y ^ 3 * τ = y ^ 3 * τ * (y ^ 3)⁻¹ * y ^ 3 := by group
        _ = τ * y ^ 3 := by rw [h3]
    have := comm_pow_mod hc hye
    rcases hes with rfl | rfl | rfl
    · exact h1 _ this (by norm_num)
    · exact h1 _ this (by norm_num)
    ·
      have h17 : (17 : ℕ) % 3 = 2 := by norm_num
      rw [h17] at this
      apply hs1
      have e2 := conj_eq_of_commute this
      rw [h2, hys] at e2
      calc s = τ⁻¹ * (τ * s) := by group
        _ = 1 := by rw [e2, inv_mul_cancel]
  · exact hs1 (by
      calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
        _ = 1 := by rw [hys]; group)

theorem pair_prod {G : Type*} [Group G] {τ s : G} (hτ2 : τ * τ = 1) : ∀ L : List G,
    (∀ g ∈ L, g * τ = τ * g ∧ (g * s * g⁻¹ = s ∨ g * s * g⁻¹ = τ * s)) →
    L.prod * s * L.prod⁻¹ = s ∨ L.prod * s * L.prod⁻¹ = τ * s
  | [], _ => Or.inl (by simp)
  | g :: L, hL => by
    obtain ⟨hgτ, hgs⟩ := hL g List.mem_cons_self
    have ih := pair_prod hτ2 L fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')
    rw [List.prod_cons]
    have e : g * L.prod * s * (g * L.prod)⁻¹ = g * (L.prod * s * L.prod⁻¹) * g⁻¹ := by group
    rw [e]
    rcases ih with ih | ih
    · rw [ih]
      exact hgs
    · rw [ih]
      have e2 : g * (τ * s) * g⁻¹ = τ * (g * s * g⁻¹) := by
        calc g * (τ * s) * g⁻¹ = g * τ * s * g⁻¹ := by group
          _ = τ * g * s * g⁻¹ := by rw [hgτ]
          _ = τ * (g * s * g⁻¹) := by group
      rw [e2]
      rcases hgs with hgs | hgs
      · exact Or.inr (by rw [hgs])
      · exact Or.inl (by rw [hgs, ← mul_assoc, hτ2, one_mul])

theorem a0_nvT : ∀ t < 8, nvT (a0Ts.getD t []) (a0TIs.getD t []) = true
  | 0, _ => ch7222nvt0
  | 1, _ => ch7222nvt1
  | 2, _ => ch7222nvt2
  | 3, _ => ch7222nvt3
  | 4, _ => ch7222nvt4
  | 5, _ => ch7222nvt5
  | 6, _ => ch7222nvt6
  | 7, _ => ch7222nvt7
  | _ + 8, h => absurd h (by omega)

theorem stk_one {x : ℕ} {g : Equiv.Perm (Fin 8330)} (h : PRep 8330 14 x g) :
    StkRep 8330 14 [x] [g] :=
  List.Forall₂.cons h List.Forall₂.nil

theorem evK_one {x : ℕ} {g : Equiv.Perm (Fin 8330)} (h : PRep 8330 14 x g) (p : Fin 8330) :
    evK 14 (mask 14) [x] p = g p := by
  rw [evK_rep (stk_one h) p, List.prod_cons, List.prod_nil, mul_one]

theorem nvS_rep
    (ht : tupOK a0Ts (getLs a0RT 4) = true) (p : Fin 8330) :
    evK 14 (mask 14) nvS p = rep0P 4 p :=
  evK_rep (stkK_rep (n := 8330) (w := 14) rec0 ht a0_hrep) p

theorem a0_nv_ent :
    ∀ t < 8, ∀ j < (a0Ts.getD t []).length,
      rec0 t j * rep0P 4 * (rec0 t j)⁻¹ = rep0P 4 ∨
        rec0 t j * rep0P 4 * (rec0 t j)⁻¹ = heGenPerm 0 * rep0P 4 := by
  intro t ht j hj
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  have r4 := hrt.1.1.1.1.1.1.1.2
  have hT := a0_hrep t ht j hj
  have hTI : PRep 8330 14 ((a0TIs.getD t []).getD j 0) (rec0 t j)⁻¹ :=
    invK_rep (by norm_num) (by norm_num) ((invLK_sound (a0_inv t ht)).2 j hj) hT
      (tree_shr (by norm_num) (by norm_num) (a0_tree t ht) j hj)
  have hnv := a0_nvT t ht
  unfold nvT at hnv
  have hk := nvLK_sound hnv j hj
  obtain ⟨hcm, -⟩ := (a0_cent_chain).1 t ht j hj
  have hsC := (prep_rep0 r4).2
  have hgP : rec0 t j * rep0P 4 * (rec0 t j)⁻¹ ∈ heP :=
    heP.mul_mem (heP.mul_mem (mem_centralizerIn.1 hcm).1 (mem_centralizerIn.1 hsC).1)
      (heP.inv_mem (mem_centralizerIn.1 hcm).1)
  have hf : ∀ p : Fin 8330, (p : ℕ) < 5 →
      cjEv 14 (mask 14) [(a0Ts.getD t []).getD j 0] nvS [(a0TIs.getD t []).getD j 0] p =
        (rec0 t j * rep0P 4 * (rec0 t j)⁻¹) p := fun p _ => by
    unfold cjEv
    rw [evK_one hTI p, nvS_rep r4, evK_one hT, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hτP := heGenPerm_mem (by norm_num : (0 : ℕ) < 2)
  rcases hk with hk | hk
  · left
    exact eq_of_keyF (f := cjEv 14 (mask 14) [(a0Ts.getD t []).getD j 0] nvS
      [(a0TIs.getD t []).getD j 0]) (f' := evK 14 (mask 14) nvS) baseFaithful_heP (by norm_num)
      hgP (mem_centralizerIn.1 hsC).1 hf (fun p _ => nvS_rep r4 p) (by norm_num) hk
  · right
    refine eq_of_keyF (f := cjEv 14 (mask 14) [(a0Ts.getD t []).getD j 0] nvS
      [(a0TIs.getD t []).getD j 0]) (f' := fun p => pg 14 (mask 14) (HG.F 0)
      (evK 14 (mask 14) nvS p)) baseFaithful_heP (by norm_num) hgP
      (heP.mul_mem hτP (mem_centralizerIn.1 hsC).1) hf (fun p _ => ?_) (by norm_num) hk
    change pg 14 (mask 14) (HG.F 0) (evK 14 (mask 14) nvS p) = _
    rw [nvS_rep r4 p, prep_a0 _, Equiv.Perm.mul_apply]

theorem a0_nv_cls
    {z : Equiv.Perm (Fin 8330)} (hz : z ∈ centralizerIn heP (heGenPerm 0)) :
    z * rep0P 4 * z⁻¹ = rep0P 4 ∨ z * rep0P 4 * z⁻¹ = heGenPerm 0 * rep0P 4 := by
  obtain ⟨f, hf, rfl⟩ := a0_cent_chain.2 z hz
  have hτ2 : heGenPerm 0 * heGenPerm 0 = 1 := by
    rw [← sq, ← orderOf_heA0]
    exact pow_orderOf_eq_one _
  refine pair_prod hτ2 _ fun g hg => ?_
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  exact ⟨(mem_centralizerIn.1 ((a0_cent_chain).1 i hi (f i) (hf i hi)).1).2,
    a0_nv_ent i hi (f i) (hf i hi)⟩

theorem a0_scan2 :
    ∀ z ∈ centralizerIn heP (heGenPerm 0), HConcl (heGenPerm 0) (hP 2 * z) := by
  intro z hz hmove he _
  exfalso
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  have r4 := hrt.1.1.1.1.1.1.1.2
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  have s2 := Nat.eq_of_beq_eq_true hsr.1.1.1.1.1.2
  have hcj := ch7222cj2
  rw [s2] at hcj
  have hτP := heGenPerm_mem (by norm_num : (0 : ℕ) < 2)
  have hτ2 : heGenPerm 0 * heGenPerm 0 = 1 := by
    rw [← sq, ← orderOf_heA0]
    exact pow_orderOf_eq_one _
  have hsC := (prep_rep0 r4).2
  have hsP := (mem_centralizerIn.1 hsC).1
  have hhP := hP_mem (j := 2) (by norm_num)
  have hhs := conj_of_cjK hcj (prep_hP (by norm_num)) prep_a0 (prep_rep0 r4).1
  have hs' : rep0P 4 = hP 2 * heGenPerm 0 * (hP 2)⁻¹ := by rw [hhs, mul_inv_cancel_right]
  have hzτ := (mem_centralizerIn.1 hz).2
  have hyτ : hP 2 * z * heGenPerm 0 * (hP 2 * z)⁻¹ = rep0P 4 := by
    calc hP 2 * z * heGenPerm 0 * (hP 2 * z)⁻¹ = hP 2 * (z * heGenPerm 0) * z⁻¹ * (hP 2)⁻¹ := by
          group
      _ = hP 2 * heGenPerm 0 * (hP 2)⁻¹ := by rw [hzτ]; group
      _ = rep0P 4 := hs'.symm
  have hs1 : rep0P 4 ≠ 1 := fun h1 => heA0_ne_one (by
    calc heGenPerm 0 = (hP 2)⁻¹ * (hP 2 * heGenPerm 0 * (hP 2)⁻¹) * hP 2 := by group
      _ = 1 := by rw [← hs', h1]; group)
  have hs2 : rep0P 4 * rep0P 4 = 1 := by
    rw [hs']
    calc hP 2 * heGenPerm 0 * (hP 2)⁻¹ * (hP 2 * heGenPerm 0 * (hP 2)⁻¹) =
        hP 2 * (heGenPerm 0 * heGenPerm 0) * (hP 2)⁻¹ := by group
      _ = 1 := by rw [hτ2, mul_one, mul_inv_cancel]
  have hts : heGenPerm 0 * rep0P 4 = rep0P 4 * heGenPerm 0 := (mem_centralizerIn.1 hsC).2.symm
  have hsτ : rep0P 4 ≠ heGenPerm 0 := fun h => hmove (by rw [hyτ, h])
  have hnv := ch7222nv
  unfold nvK at hnv
  simp only [strictB_eqP, Bool.and_eq_true, Bool.or_eq_true] at hnv
  obtain ⟨⟨hkh, -⟩, -⟩ := hnv
  have hshr := Nat.eq_of_beq_eq_true ch7222shr
  have hl : scH.length = 8 := by
    rw [← lenS_eq]
    exact Nat.eq_of_beq_eq_true ch7222hlen
  have hinv := (invLK_sound ch7222ih).2 2 (by rw [hl]; norm_num)
  have hHI : PRep 8330 14 (getS scHI 2) (hP 2)⁻¹ := by
    rw [getS_eq]
    refine invK_rep (by norm_num) (by norm_num) hinv ?_ ?_
    · rw [← getS_eq]
      exact prep_hP (by norm_num)
    · rw [← getS_eq]
      exact hshr
  have hgP : hP 2 * rep0P 4 * (hP 2)⁻¹ ∈ heP :=
    heP.mul_mem (heP.mul_mem hhP hsP) (heP.inv_mem hhP)
  have hf : ∀ p : Fin 8330, (p : ℕ) < 5 →
      pg 14 (mask 14) (getS scH 2) (evK 14 (mask 14) (stkK a0Ts (getLs a0RT 4))
        (pg 14 (mask 14) (getS scHI 2) p)) = (hP 2 * rep0P 4 * (hP 2)⁻¹) p := fun p _ => by
    rw [hHI p]
    change pg 14 (mask 14) (getS scH 2) (evK 14 (mask 14) nvS ((hP 2)⁻¹ p)) = _
    rw [nvS_rep r4, prep_hP (j := 2) (by norm_num) _, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply]
  have hhs3 : hP 2 * rep0P 4 * (hP 2)⁻¹ = heGenPerm 0 ∨ hP 2 * rep0P 4 * (hP 2)⁻¹ = rep0P 4 ∨
      hP 2 * rep0P 4 * (hP 2)⁻¹ = heGenPerm 0 * rep0P 4 := by
    rcases hkh with (hk | hk) | hk
    · exact Or.inl (eq_of_keyF (f := fun p => pg 14 (mask 14) (getS scH 2) (evK 14 (mask 14)
        (stkK a0Ts (getLs a0RT 4)) (pg 14 (mask 14) (getS scHI 2) p)))
        (f' := pg 14 (mask 14) (HG.F 0)) baseFaithful_heP (by norm_num) hgP hτP hf
        (fun p _ => prep_a0 p) (by norm_num) (Nat.eq_of_beq_eq_true hk))
    · exact Or.inr (Or.inl (eq_of_keyF (f := fun p => pg 14 (mask 14) (getS scH 2)
        (evK 14 (mask 14) (stkK a0Ts (getLs a0RT 4)) (pg 14 (mask 14) (getS scHI 2) p)))
        (f' := evK 14 (mask 14) (stkK a0Ts (getLs a0RT 4))) baseFaithful_heP (by norm_num) hgP
        hsP hf (fun p _ => nvS_rep r4 p) (by norm_num) (Nat.eq_of_beq_eq_true hk)))
    · refine Or.inr (Or.inr (eq_of_keyF (f := fun p => pg 14 (mask 14) (getS scH 2)
        (evK 14 (mask 14) (stkK a0Ts (getLs a0RT 4)) (pg 14 (mask 14) (getS scHI 2) p)))
        (f' := fun p => pg 14 (mask 14) (HG.F 0) (evK 14 (mask 14) (stkK a0Ts (getLs a0RT 4)) p))
        baseFaithful_heP (by norm_num) hgP (heP.mul_mem hτP hsP)
        hf (fun p _ => ?_) (by norm_num) (Nat.eq_of_beq_eq_true hk)))
      change pg 14 (mask 14) (HG.F 0) (evK 14 (mask 14) nvS p) = _
      rw [nvS_rep r4 p, prep_a0 _, Equiv.Perm.mul_apply]
  have hys : hP 2 * z * rep0P 4 * (hP 2 * z)⁻¹ = hP 2 * (z * rep0P 4 * z⁻¹) * (hP 2)⁻¹ := by
    group
  have hτs : hP 2 * (heGenPerm 0 * rep0P 4) * (hP 2)⁻¹ =
      rep0P 4 * (hP 2 * rep0P 4 * (hP 2)⁻¹) := by
    rw [hs']
    group
  refine nv_false hs2 hts hyτ hsτ hs1 ?_ he
  rw [hys]
  rcases a0_nv_cls hz with hx | hx <;> rw [hx]
  · rcases hhs3 with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
  · rw [hτs]
    rcases hhs3 with h3 | h3 | h3 <;> rw [h3]
    · exact Or.inr (Or.inr (Or.inl hts.symm))
    · exact Or.inr (Or.inr (Or.inr hs2))
    · refine Or.inl ?_
      rw [← mul_assoc, ← hts, mul_assoc, hs2, mul_one]

end CertificateChecks.KernelHe7222

end
