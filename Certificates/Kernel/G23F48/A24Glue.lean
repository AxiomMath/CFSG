module

public import Certificates.Kernel.G23F48.A22Glue
public import CFSG.Certificates.Kernel.G23F48.ConjCount

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)

@[expose] noncomputable def kap (j : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 (burnsideF48t_g23KArr ())[j]!

theorem prep_kap {j : ℕ} (hj : j < 2) :
    CFSG.ONSchreier.PRep 728 (burnsideF48t_g23KArr ())[j]! (kap j) ∧
      Orb.PRep 728 10 (KCh.S j) (kap j) := by
  obtain ⟨g, hg, -⟩ := CFSG.KC.EnumSound.permOK_perm (allN_spec k_perm j (by omega))
  have ht : CFSG.ONSchreier.PRep 728 (burnsideF48t_g23KArr ())[j]! g := fun x => by
    rw [kArr_get.2 j hj, Orb.unpack_get x.2]
    exact hg x
  rw [kap, onPermOfArr_eq ht]
  exact ⟨ht, hg⟩

theorem kap_mem {j : ℕ} (hj : j < 2) : kap j ∈ arrGen 728 (burnsideF48t_g23KArr ()) :=
  Subgroup.subset_closure ⟨j, by rw [kArr_get.1]; exact hj,
    CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_kap hj).1⟩

theorem pack_eq {P Q : ℕ} {g : Equiv.Perm (Fin 728)} (hP : P >>> (728 * 10) = 0)
    (hQ : Q >>> (728 * 10) = 0) (hp : Orb.PRep 728 10 P g) (hq : Orb.PRep 728 10 Q g) : P = Q :=
  PF.eq_of_fields (by norm_num) hP hQ fun i hi => (hp ⟨i, hi⟩).trans (hq ⟨i, hi⟩).symm

theorem shr_S {j : ℕ} (hj : j < 2) : KCh.S j >>> (728 * 10) = 0 :=
  (Orb.permOK_facts (allN_spec k_perm j (by omega))).1

theorem shr_LP {i : ℕ} (hi : i < 4) : LP i >>> (728 * 10) = 0 :=
  (Orb.permOK_facts (allN_spec l_perm i hi)).1

theorem shr_pidn : pidn 728 10 >>> (728 * 10) = 0 :=
  PF.pidn_shr (by norm_num) (by norm_num)

theorem kEls_ne : Nat.beq (pidn 728 10) (KCh.S 0) = false ∧ Nat.beq (pidn 728 10) (KCh.S 1) = false ∧
    Nat.beq (pidn 728 10) (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)) = false ∧
    Nat.beq (KCh.S 0) (KCh.S 1) = false ∧
    Nat.beq (KCh.S 0) (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)) = false ∧
    Nat.beq (KCh.S 1) (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)) = false := by
  decide +kernel

theorem ne_of_pack {P Q : ℕ} {g h : Equiv.Perm (Fin 728)} (hP : P >>> (728 * 10) = 0)
    (hQ : Q >>> (728 * 10) = 0) (hp : Orb.PRep 728 10 P g) (hq : Orb.PRep 728 10 Q h)
    (hne : Nat.beq P Q = false) : g ≠ h := by
  rintro rfl
  exact Nat.ne_of_beq_eq_false hne (pack_eq hP hQ hp hq)

theorem prep_k01 : Orb.PRep 728 10 (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)) (kap 0 * kap 1) :=
  Orb.prep_pcomp (by norm_num) (prep_kap (by norm_num)).2 (prep_kap (by norm_num)).2

theorem shr_k01 : pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1) >>> (728 * 10) = 0 :=
  PF.pcomp_shr _ _ (by norm_num) (by norm_num)

theorem kap_ne : kap 0 ≠ 1 ∧ kap 1 ≠ 1 ∧ kap 0 * kap 1 ≠ 1 ∧ kap 0 ≠ kap 1 ∧
    kap 0 ≠ kap 0 * kap 1 ∧ kap 1 ≠ kap 0 * kap 1 := by
  have h0 := (prep_kap (j := 0) (by norm_num)).2
  have h1 := (prep_kap (j := 1) (by norm_num)).2
  have hi := Orb.prep_pidn (n := 728) (w := 10) (by norm_num) (by norm_num)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := kEls_ne
  have s0 := shr_S (j := 0) (by norm_num)
  have s1 := shr_S (j := 1) (by norm_num)
  exact ⟨(ne_of_pack shr_pidn s0 hi h0 e1).symm, (ne_of_pack shr_pidn s1 hi h1 e2).symm,
    (ne_of_pack shr_pidn shr_k01 hi prep_k01 e3).symm, ne_of_pack s0 s1 h0 h1 e4,
    ne_of_pack s0 shr_k01 h0 prep_k01 e5, ne_of_pack s1 shr_k01 h1 prep_k01 e6⟩

theorem K_cases {c : Equiv.Perm (Fin 728)} (hc : c ∈ arrGen 728 (burnsideF48t_g23KArr ())) :
    c = 1 ∨ c = kap 0 ∨ c = kap 1 ∨ c = kap 0 * kap 1 := by
  obtain ⟨n0, n1, n01, n0_1, n0_01, n1_01⟩ := kap_ne
  have k0 := kap_mem (j := 0) (by norm_num)
  have k1 := kap_mem (j := 1) (by norm_num)
  exact eq_of_card_four card_K (Subgroup.one_mem _) k0 k1 (Subgroup.mul_mem _ k0 k1) n0.symm
    n1.symm n01.symm n0_1 n0_01 n1_01 hc

theorem mem_K_iff {X : ℕ} {c : Equiv.Perm (Fin 728)} (hX : X >>> (728 * 10) = 0)
    (hc : Orb.PRep 728 10 X c) : c ∈ arrGen 728 (burnsideF48t_g23KArr ()) ↔ X ∈ kEls := by
  have h0 := (prep_kap (j := 0) (by norm_num)).2
  have h1 := (prep_kap (j := 1) (by norm_num)).2
  have hi := Orb.prep_pidn (n := 728) (w := 10) (by norm_num) (by norm_num)
  have k0 := kap_mem (j := 0) (by norm_num)
  have k1 := kap_mem (j := 1) (by norm_num)
  constructor
  · intro hm
    simp only [kEls, List.mem_cons, List.not_mem_nil, or_false]
    rcases K_cases hm with rfl | rfl | rfl | rfl
    · exact Or.inl (pack_eq hX shr_pidn hc hi)
    · exact Or.inr (Or.inl (pack_eq hX (shr_S (by norm_num)) hc h0))
    · exact Or.inr (Or.inr (Or.inl (pack_eq hX (shr_S (by norm_num)) hc h1)))
    · exact Or.inr (Or.inr (Or.inr (pack_eq hX shr_k01 hc prep_k01)))
  · intro hm
    simp only [kEls, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [oprep_unique hc hi]
      exact Subgroup.one_mem _
    · rw [oprep_unique hc h0]
      exact k0
    · rw [oprep_unique hc h1]
      exact k1
    · rw [oprep_unique hc prep_k01]
      exact Subgroup.mul_mem _ k0 k1

theorem xy_norm {r : ℕ} (hr : r = 2 ∨ r = 3) :
    sig r ∈ Subgroup.normalizer (arrGen 728 (burnsideF48t_g23KArr ()) : Set (Equiv.Perm (Fin 728))) ∧
      sig r ∉ arrGen 728 (burnsideF48t_g23KArr ()) := by
  have hr4 : r < 4 := by omega
  have hk := k_ok.2.2.2
  rw [List.all_eq_true] at hk
  have hk' := hk r (by rcases hr with rfl | rfl <;> simp)
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk'
  obtain ⟨hc, hn⟩ := hk'
  have hl := prep_letter hr4
  refine ⟨mem_normalizer_of_conj fun c hcK => ?_, fun hm => ?_⟩
  · have hconj : ∀ t < 2, sig r * kap t * (sig r)⁻¹ ∈ arrGen 728 (burnsideF48t_g23KArr ()) := by
      intro t ht
      have hpc : Orb.PRep 728 10 (pconj 728 10 (LP r) (LPI r) (KCh.S t)) (sig r * kap t * (sig r)⁻¹) :=
        Orb.prep_pcomp (by norm_num) (Orb.prep_pcomp (by norm_num) hl.2.1 (prep_kap ht).2) hl.2.2
      refine (mem_K_iff (PF.pcomp_shr _ _ (by norm_num) (by norm_num)) hpc).2 ?_
      have := hc t (by interval_cases t <;> simp)
      exact List.contains_iff_mem.1 this
    rcases K_cases hcK with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · exact hconj 0 (by norm_num)
    · exact hconj 1 (by norm_num)
    · have e : sig r * (kap 0 * kap 1) * (sig r)⁻¹ =
          sig r * kap 0 * (sig r)⁻¹ * (sig r * kap 1 * (sig r)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hconj 0 (by norm_num)) (hconj 1 (by norm_num))
  · have := (mem_K_iff (shr_LP hr4) hl.2.1).1 hm
    rw [← List.contains_iff_mem, hn] at this
    exact Bool.false_ne_true this

@[expose] noncomputable def om (t : ℕ) (i : Fin 121) : Fin 728 :=
  ⟨pg 10 (mask 10) (OM t) i % 728, Nat.mod_lt _ (by norm_num)⟩

theorem om_facts {t : ℕ} (ht : t < 2) :
    (∀ i < 120, pg 10 (mask 10) (OM t) i < pg 10 (mask 10) (OM t) (i + 1)) ∧
      pg 10 (mask 10) (OM t) 120 < 728 := by
  have h := allN_spec om_ok t ht
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨fun i hi => ?_, h.2⟩
  have := allN_spec h.1 i hi
  rwa [Nat.blt_eq] at this

theorem om_mono {t : ℕ} (ht : t < 2) : StrictMono fun i : Fin 121 => pg 10 (mask 10) (OM t) i :=
  Fin.strictMono_iff_lt_succ.2 fun i => (om_facts ht).1 i i.2

theorem om_val {t : ℕ} (ht : t < 2) (i : Fin 121) :
    ((om t i : Fin 728) : ℕ) = pg 10 (mask 10) (OM t) i := by
  have hle := (om_mono ht).monotone (Fin.le_last i)
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hle (om_facts ht).2)

theorem om_inj {t : ℕ} (ht : t < 2) : Function.Injective (om t) := fun i j e => by
  have e' := congrArg Fin.val e
  rw [om_val ht, om_val ht] at e'
  exact (om_mono ht).injective e'

theorem relOm_of {t : ℕ} (ht : t < 2) {GP R : ℕ} {c : Equiv.Perm (Fin 728)}
    {r : Equiv.Perm (Fin 121)} (hc : Orb.PRep 728 10 GP c) (hr : Orb.PRep 121 7 R r)
    (h : allN 121 (fun i => Nat.beq (pg 10 (mask 10) GP (pg 10 (mask 10) (OM t) i))
      (pg 10 (mask 10) (OM t) (pg 7 (mask 7) R i))) = true) : RelOm (om t) c r := fun i => by
  apply Fin.ext
  rw [om_val ht, ← hc, om_val ht, Nat.eq_of_beq_eq_true (allN_spec h i i.2), hr i]

theorem rho_ex : ∀ s, ∃ r : Equiv.Perm (Fin 121) × Equiv.Perm (Fin 121), s < 5 →
    (Orb.PRep 121 7 (R1 s) r.1 ∧ Orb.PRep 121 7 (R1I s) r.1⁻¹) ∧
      (Orb.PRep 121 7 (R2 s) r.2 ∧ Orb.PRep 121 7 (R2I s) r.2⁻¹) := fun s => by
  by_cases hs : s < 5
  · have h := allN_spec r_perm s hs
    rw [Bool.and_eq_true] at h
    obtain ⟨g1, hg1, hg1i⟩ := CFSG.KC.EnumSound.permOK_perm h.1
    obtain ⟨g2, hg2, hg2i⟩ := CFSG.KC.EnumSound.permOK_perm h.2
    exact ⟨(g1, g2), fun _ => ⟨⟨hg1, hg1i⟩, hg2, hg2i⟩⟩
  · exact ⟨(1, 1), fun h => absurd h hs⟩

@[expose] noncomputable def rho (s : ℕ) : Equiv.Perm (Fin 121) × Equiv.Perm (Fin 121) :=
  Classical.choose (rho_ex s)

theorem rho_spec {s : ℕ} (hs : s < 5) :
    (Orb.PRep 121 7 (R1 s) (rho s).1 ∧ Orb.PRep 121 7 (R1I s) (rho s).1⁻¹) ∧
      (Orb.PRep 121 7 (R2 s) (rho s).2 ∧ Orb.PRep 121 7 (R2I s) (rho s).2⁻¹) :=
  Classical.choose_spec (rho_ex s) hs

theorem shr_R1 {s : ℕ} (hs : s < 5) : R1 s >>> (121 * 7) = 0 := by
  have h := allN_spec r_perm s hs
  rw [Bool.and_eq_true] at h
  exact (Orb.permOK_facts h.1).1

theorem shr_R2 {s : ℕ} (hs : s < 5) : R2 s >>> (121 * 7) = 0 := by
  have h := allN_spec r_perm s hs
  rw [Bool.and_eq_true] at h
  exact (Orb.permOK_facts h.2).1

theorem K_le_P : arrGen 728 (burnsideF48t_g23KArr ()) ≤ arrGen 728 burnsideF48t_g23P1Arr ∧
    arrGen 728 (burnsideF48t_g23KArr ()) ≤ arrGen 728 burnsideF48t_g23P2Arr :=
  ⟨K_le recL ⟨sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
      sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)⟩,
    K_le recL ⟨sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
      sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)⟩⟩

theorem card_N1 (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    Nat.card ↥(arrGen 728 burnsideF48t_g23P1Arr ⊓
      Subgroup.normalizer (arrGen 728 (burnsideF48t_g23KArr ()) : Set (Equiv.Perm (Fin 728)))) ≤
      8 := by
  obtain ⟨n0, n1, n01, n0_1, n0_01, n1_01⟩ := kap_ne
  have hG : ∀ s < [R1 0, R1 1, R1 2].length,
      Orb.PRep 121 7 ([R1 0, R1 1, R1 2].getD s 0) (rho s).1 ∧
        Orb.PRep 121 7 ([R1I 0, R1I 1, R1I 2].getD s 0) (rho s).1⁻¹ ∧
        RelOm (om 0) (sig s) (rho s).1 := by
    intro s hs
    have hs3 : s < 3 := hs
    interval_cases s
    · exact ⟨(rho_spec (s := 0) (by norm_num)).1.1, (rho_spec (s := 0) (by norm_num)).1.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).1.1
          (allN_spec r_bind.1 0 (by norm_num))⟩
    · exact ⟨(rho_spec (s := 1) (by norm_num)).1.1, (rho_spec (s := 1) (by norm_num)).1.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).1.1
          (allN_spec r_bind.1 1 (by norm_num))⟩
    · exact ⟨(rho_spec (s := 2) (by norm_num)).1.1, (rho_spec (s := 2) (by norm_num)).1.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).1.1
          (allN_spec r_bind.1 2 (by norm_num))⟩
  have hσ : ∀ s < [R1 0, R1 1, R1 2].length, sig s ∈ arrGen 728 burnsideF48t_g23P1Arr := by
    intro s hs
    have hs3 : s < 3 := hs
    interval_cases s
    · exact sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)
  have ha : Enc 121 7 (om 0) (R1 3) (kap 0) := ⟨shr_R1 (by norm_num), (rho 3).1,
    (rho_spec (by norm_num)).1.1, relOm_of (by norm_num) (prep_kap (by norm_num)).2
      (rho_spec (by norm_num)).1.1 (allN_spec r_bind.1 3 (by norm_num))⟩
  have hb : Enc 121 7 (om 0) (R1 4) (kap 1) := ⟨shr_R1 (by norm_num), (rho 4).1,
    (rho_spec (by norm_num)).1.1, relOm_of (by norm_num) (prep_kap (by norm_num)).2
      (rho_spec (by norm_num)).1.1 (allN_spec r_bind.1 4 (by norm_num))⟩
  obtain ⟨g, hgP, hgd⟩ := conj_distinct (om_inj (t := 0) (by norm_num)) (by norm_num)
    (by norm_num) conj1_ok hG hσ ha hb (fun c hc => K_cases hc) (kap_mem (by norm_num))
    (kap_mem (by norm_num)) n0 n1 n01 n0_1 n0_01 n1_01
  have h := card_mul_le_of_conj g hgP hgd
  rw [(card_P1_P2_B hX).1] at h
  omega

theorem card_N2 (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696) :
    Nat.card ↥(arrGen 728 burnsideF48t_g23P2Arr ⊓
      Subgroup.normalizer (arrGen 728 (burnsideF48t_g23KArr ()) : Set (Equiv.Perm (Fin 728)))) ≤
      8 := by
  obtain ⟨n0, n1, n01, n0_1, n0_01, n1_01⟩ := kap_ne
  have hG : ∀ s < [R2 0, R2 1, R2 2].length,
      Orb.PRep 121 7 ([R2 0, R2 1, R2 2].getD s 0) (rho s).2 ∧
        Orb.PRep 121 7 ([R2I 0, R2I 1, R2I 2].getD s 0) (rho s).2⁻¹ ∧
        RelOm (om 1) (sig (s + s / 2)) (rho s).2 := by
    intro s hs
    have hs3 : s < 3 := hs
    interval_cases s
    · exact ⟨(rho_spec (s := 0) (by norm_num)).2.1, (rho_spec (s := 0) (by norm_num)).2.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).2.1
          (allN_spec r_bind.2 0 (by norm_num))⟩
    · exact ⟨(rho_spec (s := 1) (by norm_num)).2.1, (rho_spec (s := 1) (by norm_num)).2.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).2.1
          (allN_spec r_bind.2 1 (by norm_num))⟩
    · exact ⟨(rho_spec (s := 2) (by norm_num)).2.1, (rho_spec (s := 2) (by norm_num)).2.2,
        relOm_of (by norm_num) (prep_letter (by norm_num)).2.1 (rho_spec (by norm_num)).2.1
          (allN_spec r_bind.2 2 (by norm_num))⟩
  have hσ : ∀ s < [R2 0, R2 1, R2 2].length,
      sig (s + s / 2) ∈ arrGen 728 burnsideF48t_g23P2Arr := by
    intro s hs
    have hs3 : s < 3 := hs
    interval_cases s
    · exact sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)
  have ha : Enc 121 7 (om 1) (R2 3) (kap 0) := ⟨shr_R2 (by norm_num), (rho 3).2,
    (rho_spec (by norm_num)).2.1, relOm_of (by norm_num) (prep_kap (by norm_num)).2
      (rho_spec (by norm_num)).2.1 (allN_spec r_bind.2 3 (by norm_num))⟩
  have hb : Enc 121 7 (om 1) (R2 4) (kap 1) := ⟨shr_R2 (by norm_num), (rho 4).2,
    (rho_spec (by norm_num)).2.1, relOm_of (by norm_num) (prep_kap (by norm_num)).2
      (rho_spec (by norm_num)).2.1 (allN_spec r_bind.2 4 (by norm_num))⟩
  obtain ⟨g, hgP, hgd⟩ := conj_distinct (om_inj (t := 1) (by norm_num)) (by norm_num)
    (by norm_num) conj2_ok hG hσ ha hb (fun c hc => K_cases hc) (kap_mem (by norm_num))
    (kap_mem (by norm_num)) n0 n1 n01 n0_1 n0_01 n1_01
  have h := card_mul_le_of_conj g hgP hgd
  rw [(card_P1_P2_B hX).2.1] at h
  omega

theorem xred (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696)
    {y : Equiv.Perm (Fin 728)} (hy : y ∈ arrGen 728 burnsideF48t_g23P1Arr)
    (hy2 : y ∉ arrGen 728 burnsideF48t_g23P2Arr)
    (hyK : ∀ k ∈ arrGen 728 (burnsideF48t_g23KArr ()),
      y * k * y⁻¹ ∈ arrGen 728 (burnsideF48t_g23KArr ())) :
    (sig 2)⁻¹ * y ∈ arrGen 728 (burnsideF48t_g23KArr ()) :=
  inv_mul_mem_of_card K_le_P.1 card_K (card_N1 hX)
    (sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)) (xy_norm (Or.inl rfl)).1
    (xy_norm (Or.inl rfl)).2 hy (mem_normalizer_of_conj hyK) fun h => hy2 (K_le_P.2 h)

theorem yred (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696)
    {y : Equiv.Perm (Fin 728)} (hy : y ∈ arrGen 728 burnsideF48t_g23P2Arr)
    (hy1 : y ∉ arrGen 728 burnsideF48t_g23P1Arr)
    (hyK : ∀ k ∈ arrGen 728 (burnsideF48t_g23KArr ()),
      y * k * y⁻¹ ∈ arrGen 728 (burnsideF48t_g23KArr ())) :
    (sig 3)⁻¹ * y ∈ arrGen 728 (burnsideF48t_g23KArr ()) :=
  inv_mul_mem_of_card K_le_P.2 card_K (card_N2 hX)
    (sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)) (xy_norm (Or.inr rfl)).1
    (xy_norm (Or.inr rfl)).2 hy (mem_normalizer_of_conj hyK) fun h => hy1 (K_le_P.1 h)

end CFSG.KC.G23F48

end
