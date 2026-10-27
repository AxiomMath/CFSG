module

public import Certificates.Kernel.U42Lat.Bridge
public import CFSG.Certificates.Kernel.CosetLat.AvoidSound
public import CFSG.Certificates.Kernel.CosetLat.Sound

public section

namespace CertificateChecks.KernelU42Lat.Glue

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.CosetLat
  CertificateChecks.KernelU42Lat CFSG.LocalAnalysis.RankThreeUC.S15.K21dU42Cert

theorem allIx_iff (l : List (List (List Nat))) (f : Nat → List (List Nat) → Bool) (i₀ : Nat) :
    allIx l f i₀ = true ↔ ∀ i < l.length, f (i₀ + i) (l.getD i []) = true := by
  induction l generalizing i₀ with
  | nil => simp [allIx]
  | cons x l ih =>
    change andB (f i₀ x) (allIx l f (Nat.succ i₀)) = true ↔ _
    constructor
    · intro h i hi
      obtain ⟨h0, h⟩ := andB_eq_true h
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := (ih _).1 h i (by simpa using hi)
        rwa [Nat.succ_add, ← Nat.add_succ] at this
    · intro h
      have h0 : f i₀ x = true := by simpa using h 0 (by simp)
      have h1 : allIx l f (Nat.succ i₀) = true := (ih _).2 fun i hi => by
        have := h (i + 1) (by simpa using hi)
        rwa [Nat.succ_add, ← Nat.add_succ]
      rw [h0, h1]
      rfl

theorem allIx_zero {l : List (List (List Nat))} {f : Nat → List (List Nat) → Bool}
    (h : allIx l f 0 = true) : ∀ i < l.length, f i (l.getD i []) = true := fun i hi => by
  simpa using (allIx_iff l f 0).1 h i hi

theorem notB_beq_zero {x : Nat} (h : x ≠ 0) : notB (Nat.beq x 0) = true := by
  cases x with
  | zero => exact absurd rfl h
  | succ n => rfl

theorem closure_le_of_getD {gens : List (Perm (Fin 45))} {L : Subgroup (Perm (Fin 45))}
    (h : ∀ j < gens.length, gens.getD j 1 ∈ L) : Subgroup.closure {g | g ∈ gens} ≤ L := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  have := h j hj
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

@[expose] def LL (t : ℕ) : List (Perm (Fin 45)) := ((tGens :: lat) ++ [mGens]).getD t []

noncomputable abbrev Fam (t : ℕ) : Subgroup (Perm (Fin 45)) := Subgroup.closure {g | g ∈ LL t}

@[expose] def xg (t : ℕ) : Perm (Fin 45) := (lat.getD (t - 1) []).getD 3 1

theorem LL_lt {t : ℕ} (ht : t < 6) : LL t = (tGens :: lat).getD t [] := by
  interval_cases t <;> rfl

theorem LL_pos {t : ℕ} (h0 : 0 < t) (ht : t < 6) : LL t = tGens ++ [xg t] := by
  interval_cases t <;> rfl

theorem lenF_eq {t : ℕ} (ht : t < 7) : (LL t).length = lenF t := by
  interval_cases t <;> rfl

theorem x_code {t : ℕ} (h0 : 0 < t) (ht : t < 6) : wcode 6 (xg t) = EL (2 + t) := by
  have h := hX (t - 1) (by omega)
  have e : 3 + (t - 1) = 2 + t := by omega
  rw [e] at h
  exact h.symm

theorem FG_code {t : ℕ} (ht : t < 7) :
    ∀ a < (LL t).length, FG t a = wcode 6 ((LL t).getD a 1) := by
  intro a ha
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · have ha3 : a < 3 := ha
    have e : FG 0 a = EL a := by interval_cases a <;> rfl
    rw [e]
    exact hT a ha3
  rcases Nat.lt_or_ge t 6 with h6 | h6
  · rw [LL_pos h0 h6] at ha ⊢
    have ha4 : a < 4 := ha
    rcases Nat.lt_or_ge a 3 with h3 | h3
    · have e1 : FG t a = EL a := by interval_cases t <;> interval_cases a <;> rfl
      rw [e1, List.getD_append _ _ _ _ h3]
      exact hT a h3
    · obtain rfl : a = 3 := by omega
      have e1 : FG t 3 = EL (2 + t) := by interval_cases t <;> rfl
      rw [e1, ← x_code h0 h6]
      rfl
  · obtain rfl : t = 6 := by omega
    exact hM a ha

theorem FGG_code {a b : ℕ} (ha : a < 7) (hb : b < 7) :
    ∀ l < (LL a ++ LL b).length, FGG a b l = wcode 6 ((LL a ++ LL b).getD l 1) := by
  intro l hl
  rw [List.length_append] at hl
  rcases Nat.lt_or_ge l (lenF a) with h1 | h1
  · have e1 : FGG a b l = FG a l := by
      unfold FGG
      rw [Nat.blt_eq.mpr h1]
    rw [e1, List.getD_append _ _ _ _ (by rw [lenF_eq ha]; exact h1)]
    exact FG_code ha l (by rw [lenF_eq ha]; exact h1)
  · have hf : Nat.blt l (lenF a) = false := by
      cases h : Nat.blt l (lenF a)
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt.2 h1)
    have e1 : FGG a b l = FG b (l - lenF a) := by
      unfold FGG
      rw [hf]
      rfl
    rw [e1, List.getD_append_right _ _ _ _ (by rw [lenF_eq ha]; exact h1), lenF_eq ha]
    exact FG_code hb _ (by rw [lenF_eq ha] at hl; omega)

theorem word_mem {t : ℕ} (ht : t < 7) {w : List ℕ} {x : Perm (Fin 45)}
    (h : wordAt mU oneU (FG t) (lenF t) w (wcode 6 x) = true) : x ∈ Fam t := by
  rw [← lenF_eq ht] at h
  exact mem_of_wordAt henc (LL t) (FG_code ht) h

theorem T_le {t : ℕ} (ht : t < 6) : Fam 0 ≤ Fam t := by
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact le_rfl
  · refine Subgroup.closure_mono fun g hg => ?_
    change g ∈ LL t
    rw [LL_pos h0 ht]
    exact List.mem_append_left _ hg

theorem Fam_le {t : ℕ} (ht : t < 6) {L : Subgroup (Perm (Fin 45))} (hT : Fam 0 ≤ L)
    (hx : 0 < t → xg t ∈ L) : Fam t ≤ L := by
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact hT
  · change Subgroup.closure {g | g ∈ LL t} ≤ L
    rw [Subgroup.closure_le]
    intro g hg
    change g ∈ LL t at hg
    rw [LL_pos h0 ht] at hg
    rcases List.mem_append.1 hg with h | h
    · exact hT (Subgroup.subset_closure h)
    · rw [List.mem_singleton.1 h]
      exact hx h0

theorem inc_M (i : ℕ) (hi : i < 8) {x : Perm (Fin 45)} (hx : wcode 6 x = EL i) : x ∈ Fam 6 := by
  have h := (allN_iff _ _).1 (andB_eq_true ch409001inc).1 i hi
  have h' : wordAt mU oneU (FG 6) (lenF 6) (getW incW i) (wcode 6 x) = true := by
    rw [hx]
    exact h
  exact word_mem (by norm_num) h'

theorem T_le_M : Fam 0 ≤ Fam 6 :=
  closure_le_of_getD fun j hj => inc_M j (by have : j < 3 := hj; omega) (hT j hj).symm

theorem Fam_le_M {t : ℕ} (ht : t < 6) : Fam t ≤ Fam 6 :=
  Fam_le ht T_le_M fun h0 => inc_M (2 + t) (by omega) (x_code h0 ht)

theorem M_le_L5 : Fam 6 ≤ Fam 5 := by
  refine closure_le_of_getD fun j hj => ?_
  have h := (allN_iff _ _).1 (andB_eq_true ch409001inc).2 j hj
  have h' : wordAt mU oneU (FG 5) (lenF 5) (getW incW (8 + j)) (wcode 6 (mGens.getD j 1)) =
      true := by
    rw [← hM j hj]
    exact h
  exact word_mem (by norm_num) h'

theorem L5_eq_M : Fam 5 = Fam 6 := le_antisymm (Fam_le_M (by norm_num)) M_le_L5

noncomputable def rho (j : ℕ) : Perm (Fin 45) :=
  open scoped Classical in if h : ∃ g : Perm (Fin 45), wcode 6 g = RC j then h.choose else 1

theorem rep_rec (j : ℕ) (hj : j < 24) : ∃ t < 6,
    (t ≠ 0 → wordAt mU oneU (TR j) 4 (getW (repW.getD j []) 1) (EL (2 + t)) = true) ∧
      wordAt mU oneU (FG t) (lenF t) (getW (repW.getD j []) 2) (RC j) = true := by
  obtain ⟨hl, hall⟩ := andB_eq_true ch409001rep
  have h : repAt j (repW.getD j []) = true :=
    allIx_zero hall j (by rw [Nat.eq_of_beq_eq_true hl]; exact hj)
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨ht6, h⟩ := andB_eq_true h
  obtain ⟨hx, hρ⟩ := andB_eq_true h
  exact ⟨_, Nat.blt_eq.mp ht6, fun h0 => impB_eq_true hx (notB_beq_zero h0), hρ⟩

theorem rho_code (j : ℕ) (hj : j < 24) : wcode 6 (rho j) = RC j := by
  obtain ⟨t, ht, -, hw⟩ := rep_rec j hj
  rw [← lenF_eq (by omega)] at hw
  obtain ⟨h1, h2⟩ := andB_eq_true hw
  obtain ⟨g, -, hge⟩ := wordG_mem henc (LL t) (FG_code (by omega)) h1
  have hex : ∃ g : Perm (Fin 45), wcode 6 g = RC j := ⟨g, hge.trans (Nat.eq_of_beq_eq_true h2)⟩
  unfold rho
  rw [dif_pos hex]
  exact hex.choose_spec

theorem UE_zero : Nat.beq (UE 0) oneU = true := (andB_eq_true ch409001u).1

theorem U_trans : ∀ i < 405, transAt mU RC 24 TE 64 UE UR i = true :=
  (allN_iff _ _).1 (andB_eq_true ch409001u).2

theorem U_code : ∀ i < 405, ∃ u : Perm (Fin 45), wcode 6 u = UE i := fun i hi => by
  obtain ⟨a, -, e, -, he⟩ := trans_sound henc rho_code T_codes U_trans i hi
  exact ⟨_, he⟩

theorem M_tab : ∀ i < 405, ctabAt mU (FG 6) (LL 6).length TE 64 UE 405 CR i = true := by
  have h : ∀ c < 3, allR (135 * c) 135 (ctabAt mU (FG 6) 2 TE 64 UE 405 CR) = true := by
    intro c hc
    interval_cases c
    · exact ch409001m0
    · exact ch409001m1
    · exact ch409001m2
  intro i hi
  exact forall_of_chunks 135 3 _ h i (by omega)

theorem M_cover : ∀ σ ∈ Fam 6, ∃ a < 24, ∃ π ∈ Fam 0, ∃ κ ∈ Fam 0, σ = π * rho a * κ :=
  ctab_cover henc (LL 6) (FG_code (by norm_num)) rho_code T_codes U_trans (by norm_num) UE_zero
    M_tab

theorem M_le : Nat.card (Fam 6) ≤ 25920 := by
  have := ctab_card henc (LL 6) (FG_code (by norm_num)) T_codes U_code (by norm_num) UE_zero M_tab
  rwa [T_full.1] at this

theorem mem_tab {t n o : ℕ} (h0 : 0 < t) (ht : t < 6) (h : memOK t n o = true) :
    (∀ i < n, ∃ u : Perm (Fin 45), wcode 6 u = UE (MJ (Nat.add o i))) ∧
    Nat.beq (UE (MJ (Nat.add o 0))) oneU = true ∧
    ∀ i < n, ctabAt mU (FG t) (LL t).length TE 64 (fun i => UE (MJ (Nat.add o i))) n
      (fun r => CR (Nat.add (Nat.add 810 (Nat.mul 4 o)) r)) i = true := by
  obtain ⟨hm0, h⟩ := andB_eq_true h
  obtain ⟨hmj, hc⟩ := andB_eq_true h
  refine ⟨fun i hi => U_code _ (Nat.blt_eq.mp ((allN_iff _ _).1 hmj i hi)), ?_, ?_⟩
  · change Nat.beq (UE (MJ o)) oneU = true
    rw [Nat.eq_of_beq_eq_true hm0]
    exact UE_zero
  · rw [lenF_eq (by omega)]
    have hl : lenF t = 4 := by interval_cases t <;> rfl
    rw [hl]
    exact (allN_iff _ _).1 hc

theorem mem_le {t n o : ℕ} (h0 : 0 < t) (ht : t < 6) (hn : 0 < n) (h : memOK t n o = true) :
    Nat.card (Fam t) ≤ 64 * n := by
  obtain ⟨hU, h1, hc⟩ := mem_tab h0 ht h
  have := ctab_card henc (LL t) (FG_code (by omega)) T_codes hU hn h1 hc
  rwa [T_full.1] at this

theorem sub_dvd {t N nK oE oC oK : ℕ} (ht : t < 7) (hN : 0 < N)
    (h : subOK t N nK oE oC oK = true) : N ∣ Nat.card (Fam t) := by
  obtain ⟨hw, hl⟩ := andB_eq_true h
  have hK : ∀ j < nK, ∃ g ∈ Fam t, wcode 6 g = SK (Nat.add oK j) := by
    intro j hj
    obtain ⟨h1, h2⟩ := andB_eq_true ((allN_iff _ _).1 hw j hj)
    rw [← lenF_eq ht] at h1
    obtain ⟨g, hg, hge⟩ := wordG_mem henc (LL t) (FG_code ht) h1
    exact ⟨g, hg, hge.trans (Nat.eq_of_beq_eq_true h2)⟩
  have hl' := (allN_iff _ _).1 hl
  exact dvd_card_of_clos henc hK hN (fun k hk => (andB_eq_true (hl' k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).2)

theorem T_dvd {t : ℕ} (ht : t < 7) : 64 ∣ Nat.card (Fam t) := by
  rw [← T_full.1]
  rcases Nat.lt_or_ge t 6 with h6 | h6
  · exact Subgroup.card_dvd_of_le (T_le h6)
  · obtain rfl : t = 6 := by omega
    exact Subgroup.card_dvd_of_le T_le_M

theorem dvd_of_lcm {a b c n : ℕ} (h : Nat.lcm a b = c) (ha : a ∣ n) (hb : b ∣ n) : c ∣ n := by
  rw [← h]
  exact Nat.lcm_dvd ha hb

theorem card_L1 : Nat.card (Fam 1) = 192 :=
  card_eq_of_dvd_of_le
    (dvd_of_lcm (by decide) (T_dvd (by norm_num)) (sub_dvd (by norm_num) (by norm_num) ch409001s1))
    (mem_le (by norm_num) (by norm_num) (by norm_num) ch409001L1)

theorem card_L2 : Nat.card (Fam 2) = 192 :=
  card_eq_of_dvd_of_le
    (dvd_of_lcm (by decide) (T_dvd (by norm_num)) (sub_dvd (by norm_num) (by norm_num) ch409001s2))
    (mem_le (by norm_num) (by norm_num) (by norm_num) ch409001L2)

theorem card_L3 : Nat.card (Fam 3) = 576 :=
  card_eq_of_dvd_of_le
    (dvd_of_lcm (by decide) (T_dvd (by norm_num)) (sub_dvd (by norm_num) (by norm_num) ch409001s3))
    (mem_le (by norm_num) (by norm_num) (by norm_num) ch409001L3)

theorem card_L4 : Nat.card (Fam 4) = 960 :=
  card_eq_of_dvd_of_le
    (dvd_of_lcm (a := 192) (b := 5) (by decide)
      (dvd_of_lcm (a := 64) (b := 3) (by decide) (T_dvd (by norm_num))
        (sub_dvd (by norm_num) (by norm_num) ch409001s4a))
      (sub_dvd (by norm_num) (by norm_num) ch409001s4b))
    (mem_le (by norm_num) (by norm_num) (by norm_num) ch409001L4)

theorem card_M : Nat.card (Fam 6) = 25920 :=
  card_eq_of_dvd_of_le
    (dvd_of_lcm (a := 5184) (b := 5) (by decide)
      (dvd_of_lcm (a := 64) (b := 81) (by decide) (T_dvd (by norm_num))
        (sub_dvd (by norm_num) (by norm_num) ch409001sM81))
      (sub_dvd (by norm_num) (by norm_num) ch409001sM5))
    M_le

theorem card_Fam (j : ℕ) (hj : j < 6) : Nat.card (Fam j) = sizes.getD j 0 := by
  interval_cases j
  · exact T_full.1
  · exact card_L1
  · exact card_L2
  · exact card_L3
  · exact card_L4
  · rw [L5_eq_M]
    exact card_M

theorem getD_three (x : Perm (Fin 45)) : (tGens ++ [x]).getD 3 1 = x := rfl

theorem TR_code (j : ℕ) (hj : j < 24) :
    ∀ a < (tGens ++ [rho j]).length, TR j a = wcode 6 ((tGens ++ [rho j]).getD a 1) := by
  intro a ha
  rcases Nat.lt_or_ge a 3 with h3 | h3
  · have e1 : TR j a = EL a := by
      unfold TR
      rw [Nat.blt_eq.mpr h3]
    rw [e1, List.getD_append _ _ _ _ h3]
    exact hT a h3
  · have ha4 : a < 4 := ha
    obtain rfl : a = 3 := by omega
    have e1 : TR j 3 = RC j := rfl
    rw [e1, getD_three, rho_code j hj]

theorem rep_join (j : ℕ) (hj : j < 24) :
    ∃ t < 6, Fam 0 ⊔ Subgroup.closure {rho j} = Fam t := by
  obtain ⟨t, ht, hx, hρ⟩ := rep_rec j hj
  have hρ' : wordAt mU oneU (FG t) (lenF t) (getW (repW.getD j []) 2) (wcode 6 (rho j)) = true := by
    rw [rho_code j hj]
    exact hρ
  refine ⟨t, ht, le_antisymm (sup_le (T_le ht) ?_) (Fam_le ht le_sup_left fun h0 => ?_)⟩
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact word_mem (by omega) hρ'
  · have hw : wordAt mU oneU (TR j) (tGens ++ [rho j]).length (getW (repW.getD j []) 1)
        (wcode 6 (xg t)) = true := by
      rw [x_code h0 ht]
      exact hx (by omega)
    have hm := mem_of_wordAt henc (tGens ++ [rho j]) (TR_code j hj) hw
    refine (Subgroup.closure_le _).2 (fun g hg => ?_) hm
    rcases List.mem_append.1 hg with h | h
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
    · rw [List.mem_singleton.1 h]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

theorem join_eq (a b : ℕ) (ha : a < 6) (hb : b < 6) : ∃ c < 6, Fam a ⊔ Fam b = Fam c := by
  obtain ⟨hj1, hj2⟩ := andB_eq_true ch409001join
  have hex := notB_eq_true ((allN_iff _ _).1 ((allN_iff _ _).1 hj2 a ha) b hb)
  obtain ⟨i, hi, hf⟩ : ∃ i < joinW.length, notB (andB (Nat.beq (nth (getW (joinW.getD i []) 0) 0) a)
      (Nat.beq (nth (getW (joinW.getD i []) 0) 1) b)) = false := by
    by_contra hne
    have : allIx joinW (fun _ e => notB (andB (Nat.beq (nth (getW e 0) 0) a)
        (Nat.beq (nth (getW e 0) 1) b))) 0 = true :=
      (allIx_iff _ _ _).2 fun i hi =>
        Bool.eq_true_of_ne_false fun hf => hne ⟨i, hi, hf⟩
    rw [this] at hex
    exact Bool.noConfusion hex
  have hab : andB (Nat.beq (nth (getW (joinW.getD i []) 0) 0) a)
      (Nat.beq (nth (getW (joinW.getD i []) 0) 1) b) = true := by
    revert hf
    cases andB (Nat.beq (nth (getW (joinW.getD i []) 0) 0) a)
      (Nat.beq (nth (getW (joinW.getD i []) 0) 1) b)
    · intro h
      exact absurd h (by decide)
    · intro _
      rfl
  obtain ⟨ea', eb'⟩ := andB_eq_true hab
  have h : joinAt (joinW.getD i []) = true := allIx_zero hj1 i hi
  unfold joinAt at h
  rw [letB_eq, letB_eq, letB_eq, Nat.eq_of_beq_eq_true ea', Nat.eq_of_beq_eq_true eb'] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨hc6, h⟩ := andB_eq_true h
  obtain ⟨hxc, h⟩ := andB_eq_true h
  obtain ⟨hxa, hxb⟩ := andB_eq_true h
  have hc : nth (getW (joinW.getD i []) 0) 2 < 6 := Nat.blt_eq.mp hc6
  have hxm : ∀ {s : ℕ}, s < 6 → 0 < s →
      wordAt mU oneU (FG (nth (getW (joinW.getD i []) 0) 2))
        (lenF (nth (getW (joinW.getD i []) 0) 2)) (getW (joinW.getD i []) 2) (EL (2 + s)) = true ∨
      wordAt mU oneU (FG (nth (getW (joinW.getD i []) 0) 2))
        (lenF (nth (getW (joinW.getD i []) 0) 2)) (getW (joinW.getD i []) 3) (EL (2 + s)) = true →
      xg s ∈ Fam (nth (getW (joinW.getD i []) 0) 2) := by
    intro s hs h0 hw
    rcases hw with hw | hw
    · have hw' : wordAt mU oneU (FG (nth (getW (joinW.getD i []) 0) 2))
          (lenF (nth (getW (joinW.getD i []) 0) 2)) (getW (joinW.getD i []) 2)
          (wcode 6 (xg s)) = true := by
        rw [x_code h0 hs]
        exact hw
      exact word_mem (by omega) hw'
    · have hw' : wordAt mU oneU (FG (nth (getW (joinW.getD i []) 0) 2))
          (lenF (nth (getW (joinW.getD i []) 0) 2)) (getW (joinW.getD i []) 3)
          (wcode 6 (xg s)) = true := by
        rw [x_code h0 hs]
        exact hw
      exact word_mem (by omega) hw'
  refine ⟨_, hc, le_antisymm (sup_le
    (Fam_le ha (T_le hc) fun h0 =>
      hxm ha h0 (Or.inl (impB_eq_true hxa (notB_beq_zero (by omega)))))
    (Fam_le hb (T_le hc) fun h0 =>
      hxm hb h0 (Or.inr (impB_eq_true hxb (notB_beq_zero (by omega))))))
    (Fam_le hc ((T_le ha).trans le_sup_left) fun h0 => ?_)⟩
  have hw : wordAt mU oneU (FGG a b) (LL a ++ LL b).length (getW (joinW.getD i []) 1)
      (wcode 6 (xg (nth (getW (joinW.getD i []) 0) 2))) = true := by
    rw [x_code h0 hc, List.length_append, lenF_eq (by omega), lenF_eq (by omega)]
    exact impB_eq_true hxc (notB_beq_zero (by omega))
  have hm := mem_of_wordAt henc (LL a ++ LL b) (FGG_code (by omega) (by omega)) hw
  refine (Subgroup.closure_le _).2 (fun g hg => ?_) hm
  rcases List.mem_append.1 hg with h | h
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure h)

theorem overgroups : ∀ Z : Subgroup (Perm (Fin 45)), Fam 0 ≤ Z → Z ≤ Fam 6 → ∃ i < 6, Fam i = Z :=
  lat_overgroups_of (Q := Fam) (ρ := rho) (by norm_num : 0 < 6) rfl (fun i hi => T_le hi)
    M_cover rep_join fun a ha b hb => join_eq a b ha hb

theorem d0_parts : SK 2 = EL 34 ∧ SK 3 = EL 35 ∧
    Nat.beq (mU (mU (EL 34) (EL 34)) (EL 34)) oneU = true ∧
    Nat.beq (mU (mU (EL 35) (EL 35)) (EL 35)) oneU = true ∧
    ∀ i < 9, allCosAt mU TE 64 (fun i => UE (MJ (Nat.add 6 i)))
      (invPairAt mU (EL 34) (mU (EL 34) (EL 34)) (EL 35) (mU (EL 35) (EL 35))) i = true := by
  obtain ⟨h1, h⟩ := andB_eq_true ch409001d0
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h5⟩ := andB_eq_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, h4, (allN_iff _ _).1 h5⟩

theorem cube_one {x : Perm (Fin 45)} {i : ℕ} (hx : EL i = wcode 6 x)
    (h : Nat.beq (mU (mU (EL i) (EL i)) (EL i)) oneU = true) : x * x * x = 1 := by
  apply henc.inj
  rw [henc.enc_mul, henc.enc_mul, henc.enc_one, ← hx]
  exact Nat.eq_of_beq_eq_true h

theorem E_codes : ∀ j < [ea, eb].length, SK (Nat.add 2 j) = wcode 6 ([ea, eb].getD j 1) := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact d0_parts.1.trans hEA
  · exact d0_parts.2.1.trans hEB

theorem E_facts : ea ∈ Fam 3 ∧ eb ∈ Fam 3 ∧ Nat.card (Subgroup.closure {g | g ∈ [ea, eb]}) = 9 := by
  obtain ⟨hw, hl⟩ := andB_eq_true ch409001s3
  have hm : ∀ j < 2, ∀ x : Perm (Fin 45), SK (Nat.add 2 j) = wcode 6 x → x ∈ Fam 3 := by
    intro j hj x hx
    have h := (allN_iff _ _).1 hw j hj
    have h' : wordAt mU oneU (FG 3) (lenF 3) (getW subW (Nat.add 2 j)) (wcode 6 x) = true := by
      rw [← hx]
      exact h
    exact word_mem (by norm_num) h'
  refine ⟨hm 0 (by norm_num) ea (E_codes 0 (by norm_num)), hm 1 (by norm_num) eb
    (E_codes 1 (by norm_num)), ?_⟩
  have hl' := (allN_iff _ _).1 hl
  obtain ⟨-, -, h3⟩ := clos_card henc [ea, eb] E_codes (N := 9) (by norm_num)
    (fun k hk => (andB_eq_true (hl' k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).1)
  exact (h3 fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).2).1

theorem d0_facts :
    ea ∈ Fam 3 ∧ eb ∈ Fam 3 ∧ Nat.card (Subgroup.closure {g | g ∈ [ea, eb]}) = 9 ∧
    ea * ea * ea = 1 ∧ eb * eb * eb = 1 ∧
    ∀ v ∈ Fam 3, ¬ (v * ea * v⁻¹ = ea⁻¹ ∧ v * eb * v⁻¹ = eb⁻¹) := by
  obtain ⟨-, -, h3a, h3b, hcos⟩ := d0_parts
  have ha3 := cube_one hEA h3a
  have hb3 := cube_one hEB h3b
  obtain ⟨hU, h1, hc⟩ := mem_tab (t := 3) (n := 9) (o := 6) (by norm_num) (by norm_num)
    ch409001L3
  have hBc := ctab_sound henc (LL 3) (FG_code (by norm_num)) T_codes hU (by norm_num) h1 hc
  refine ⟨E_facts.1, E_facts.2.1, E_facts.2.2, ha3, hb3, ?_⟩
  exact no_inv_pair henc T_full.2 hBc hEA.symm (by rw [henc.enc_mul, hEA]) hEB.symm
    (by rw [henc.enc_mul, hEB]) ha3 hb3 hcos

theorem facts :
    (Subgroup.closure {g | g ∈ tGens} ≤ Subgroup.closure {g | g ∈ mGens} ∧
      Nat.card (Subgroup.closure {g | g ∈ tGens}) = 64 ∧
      Nat.card (Subgroup.closure {g | g ∈ mGens}) = 25920) ∧
    ((∀ j < 6, Subgroup.closure {g | g ∈ (tGens :: lat).getD j []} ≤
        Subgroup.closure {g | g ∈ mGens} ∧
        Nat.card (Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) = sizes.getD j 0) ∧
      ∀ Y : Subgroup (Perm (Fin 45)), Subgroup.closure {g | g ∈ tGens} ≤ Y →
        Y ≤ Subgroup.closure {g | g ∈ mGens} →
        ∃ j < 6, Y = Subgroup.closure {g | g ∈ (tGens :: lat).getD j []}) ∧
    (ea ∈ Subgroup.closure {g | g ∈ L3} ∧ eb ∈ Subgroup.closure {g | g ∈ L3} ∧
      Nat.card (Subgroup.closure {g | g ∈ [ea, eb]}) = 9 ∧ ea * ea * ea = 1 ∧
      eb * eb * eb = 1 ∧
      ∀ v ∈ Subgroup.closure {g | g ∈ L3}, ¬ (v * ea * v⁻¹ = ea⁻¹ ∧ v * eb * v⁻¹ = eb⁻¹)) := by
  refine ⟨⟨T_le_M, T_full.1, card_M⟩, ⟨fun j hj => ?_, fun Y hTY hYM => ?_⟩, d0_facts⟩
  · rw [← LL_lt hj]
    exact ⟨Fam_le_M hj, card_Fam j hj⟩
  · obtain ⟨i, hi, hQ⟩ := overgroups Y hTY hYM
    refine ⟨i, hi, ?_⟩
    rw [← LL_lt hi]
    exact hQ.symm

end CertificateChecks.KernelU42Lat.Glue

end
