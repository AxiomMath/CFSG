module

public import Certificates.Kernel.HN1408.CoverFacts
public import Certificates.Kernel.HN1408.TabXCntChk

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TabX

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem cntN_eq' (f : Nat → Bool) :
    ∀ m, cntN m f = ((Finset.range m).filter fun i => f i = true).card
  | 0 => rfl
  | m + 1 => by
    change strictN (cntN m f) (fun a => Nat.add a (Bool.rec (motive := fun _ => Nat) 0 1 (f m))) = _
    rw [strictN_eq', cntN_eq' f m, Finset.range_add_one, Finset.filter_insert]
    cases hf : f m
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

noncomputable def czSet (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) (n : Nat) :
    Finset (Nat × Nat) :=
  (Finset.range n ×ˢ Finset.range 24).filter fun p => F (T0 p.1) (T1 p.2) = true

theorem czSet_succ (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) (n : Nat) :
    (czSet T0 T1 F (n + 1)).card =
      (czSet T0 T1 F n).card + ((Finset.range 24).filter fun j => F (T0 n) (T1 j) = true).card := by
  have hinj : Function.Injective fun j : Nat => (n, j) := fun a b h => (Prod.mk.inj h).2
  have hd : Disjoint (czSet T0 T1 F n)
      (((Finset.range 24).filter fun j => F (T0 n) (T1 j) = true).image fun j => (n, j)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [czSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    exact lt_irrefl _ hp.1.1
  have he : czSet T0 T1 F (n + 1) = czSet T0 T1 F n ∪
      (((Finset.range 24).filter fun j => F (T0 n) (T1 j) = true).image fun j => (n, j)) := by
    ext ⟨i, j⟩
    rw [Finset.mem_union, Finset.mem_image]
    simp only [czSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hi, hj⟩, hF⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact Or.inl ⟨⟨hi, hj⟩, hF⟩
      · subst hi
        exact Or.inr ⟨j, ⟨hj, hF⟩, rfl, rfl⟩
    · rintro (⟨⟨hi, hj⟩, hF⟩ | ⟨j', ⟨hj, hF⟩, hn, hj'⟩)
      · exact ⟨⟨by omega, hj⟩, hF⟩
      · subst hn hj'
        exact ⟨⟨by omega, hj⟩, hF⟩
  rw [he, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinj]

theorem czCnt_rec (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) :
    ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i ih => strictN ih fun a =>
        Nat.add a (strictN (T0 i) fun A => cntN 24 fun j => F A (T1 j))) n =
        (czSet T0 T1 F n).card
  | 0 => rfl
  | n + 1 => by
    change strictN _ (fun a => Nat.add a (strictN (T0 n) fun A => cntN 24 fun j => F A (T1 j))) = _
    rw [strictN_eq', strictN_eq', czCnt_rec T0 T1 F n, czSet_succ, cntN_eq']
    rfl

theorem czCnt_eq (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) :
    czCnt T0 T1 F = (czSet T0 T1 F 1280).card :=
  czCnt_rec T0 T1 F 1280

theorem ncard_eq_czCnt (hP : Nat.card ↥P1408 = 177408000) {F : Nat → Nat → Bool}
    {Q : Equiv.Perm (Fin 1408) → Prop}
    (hQ : ∀ i < 1280, ∀ j < 24, (F (T0 i) (T1 j) = true ↔ Q (t0P i * t1P j))) :
    {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧ Q g}.ncard =
      czCnt T0 T1 F := by
  classical
  rw [czCnt_eq]
  have hinj : Set.InjOn (fun p : Nat × Nat => t0P p.1 * t1P p.2) ↑(czSet T0 T1 F 1280) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [czSet, Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
      at hp hp'
    obtain ⟨h1, h2⟩ := el_inj hp.1.1 hp'.1.1 hp.1.2 hp'.1.2 e
    rw [h1, h2]
  have himg : {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧ Q g} =
      ↑((czSet T0 T1 F 1280).image fun p => t0P p.1 * t1P p.2) := by
    ext g
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, czSet, Finset.coe_filter,
      Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨hg, hq⟩
      obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
      exact ⟨i, j, ⟨⟨hi, hj⟩, (hQ i hi j hj).2 hq⟩, rfl⟩
    · rintro ⟨i, j, ⟨⟨hi, hj⟩, hF⟩, rfl⟩
      exact ⟨(mem_iff hP).2 ⟨i, hi, j, hj, rfl⟩, (hQ i hi j hj).1 hF⟩
  rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

theorem commB_iff (hP : Nat.card ↥P1408 = 177408000) {H : Nat} {h : Equiv.Perm (Fin 1408)}
    (hH : RepC H h) (hh : h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    {i j : Nat} (hi : i < 1280) (hj : j < 24) :
    commB (T0 i) (T1 j) H (pt (T0 i) (pt (T1 j) 0)) (pt (T0 i) (pt (T1 j) 1)) = true ↔
      (t0P i * t1P j) * h = h * (t0P i * t1P j) := by
  have hev : ∀ x (hx : x < 1408), pt (T0 i) (pt (T1 j) x) = ((t0P i * t1P j) ⟨x, hx⟩).val :=
    fun x hx => ev_eq hi hj hx
  refine ⟨fun hc => ?_, commB_of hev hH⟩
  have hg := CzInv.mem_cz hP hi hj
  unfold commB at hc
  obtain ⟨a, b⟩ := mkA hc
  have e : ∀ x (hx : x < 1408), x < 2 →
      Nat.beq (pt (T0 i) (pt (T1 j) (pt H x))) (pt H (pt (T0 i) (pt (T1 j) x))) = true →
        ((t0P i * t1P j) * h) ⟨x, hx⟩ = (h * (t0P i * t1P j)) ⟨x, hx⟩ := by
    intro x hx _ hb
    have hy : pt H x < 1408 := pt_lt hH.1 hx
    have hgx : pt (T0 i) (pt (T1 j) x) < 1408 := by rw [hev x hx]; exact Fin.isLt _
    have e1 := Nat.eq_of_beq_eq_true hb
    rw [hev _ hy, repC_pt hH hgx] at e1
    apply Fin.ext
    simp only [Equiv.Perm.mul_apply]
    have hfx : (⟨pt H x, hy⟩ : Fin 1408) = h ⟨x, hx⟩ := Fin.ext (repC_pt hH hx)
    have hfg : (⟨pt (T0 i) (pt (T1 j) x), hgx⟩ : Fin 1408) = (t0P i * t1P j) ⟨x, hx⟩ :=
      Fin.ext (hev x hx)
    rw [hfx, hfg] at e1
    simpa only [Equiv.Perm.mul_apply] using e1
  exact eq_of_base hP (mul_mem hg hh) (mul_mem hh hg) (e 0 (by norm_num) (by norm_num) a)
    (e 1 (by norm_num) (by norm_num) b)

theorem card_cent_of_stabK (hP : Nat.card ↥P1408 = 177408000) {H n : Nat}
    {h : Equiv.Perm (Fin 1408)} (hH : RepC H h)
    (hh : h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hk : stabK H n = true) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) = n := by
  have hc : stabCnt H = n := Nat.eq_of_beq_eq_true hk
  unfold stabCnt at hc
  rw [strictN_eq'] at hc
  have hs : ((P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408))) : Subgroup (Equiv.Perm (Fin 1408))) :
        Set (Equiv.Perm (Fin 1408))) =
      {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧ g * h = h * g} := by
    ext g
    rw [SetLike.mem_coe, mem_inf, Set.mem_setOf_eq, mem_centralizer_singleton_iff]
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) =
      ((P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({h} : Set (Equiv.Perm (Fin 1408))) : Subgroup (Equiv.Perm (Fin 1408))) :
          Set (Equiv.Perm (Fin 1408))).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hs, ncard_eq_czCnt hP
    (F := fun A B => commB A B H (pt A (pt B 0)) (pt A (pt B 1))) (Q := fun g => g * h = h * g)
    (fun i hi j hj => commB_iff hP hH hh hi hj), hc]

theorem card_cent_b (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) = 768 := by
  obtain ⟨hq, hq', he⟩ := CzInv.named_eq hP (c := 3) (by norm_num)
  have hb : CzInv.namedA 3 = elemB := by simp [CzInv.namedA, CzInv.namedE]
  rw [hb] at he
  have hmem : elemB ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← he]
    exact CzInv.mem_cz hP hq hq'
  exact card_cent_of_stabK hP (repC_word (by decide)) hmem stab0_ok

noncomputable def c1E : Equiv.Perm (Fin 1408) := t0P 817 * t1P 0

theorem c1E_mem (hP : Nat.card ↥P1408 = 177408000) :
    c1E ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  CzInv.mem_cz hP (by norm_num) (by norm_num)

theorem card_cent_c1 (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({c1E} : Set (Equiv.Perm (Fin 1408)))) = 384 :=
  card_cent_of_stabK hP (repC_pc (t0P_spec (by norm_num)).2 (t1P_spec (by norm_num)).2)
    (c1E_mem hP) stab1_ok

end CFSG.KD.HN1408.TabX

end
