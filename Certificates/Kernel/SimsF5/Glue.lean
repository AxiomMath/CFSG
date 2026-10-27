module

public import CFSG.Quasithin.Background.SimsF5LatInputs
public import Certificates.Kernel.SimsF5.Checks
public import CFSG.Certificates.Kernel.SimsF5.Sound
public import CFSG.Certificates.Kernel.CosetLat.Sound

public section

namespace CertificateChecks.KernelSimsF5

open CFSG.Quasithin.SimsF5Lat CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat
  CFSG.KC.SimsF5

theorem andB_true_iff7600 {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem allIx_iff (l : List (List (List Nat))) (f : Nat → List (List Nat) → Bool) (i₀ : Nat) :
    allIx l f i₀ = true ↔ ∀ i < l.length, f (i₀ + i) (l.getD i []) = true := by
  induction l generalizing i₀ with
  | nil => simp [allIx]
  | cons x l ih =>
    change andB (f i₀ x) (allIx l f (Nat.succ i₀)) = true ↔ _
    rw [andB_true_iff7600, ih]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h i (by simpa using hi)
        rwa [Nat.succ_add, ← Nat.add_succ] at this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      rwa [Nat.succ_add, ← Nat.add_succ]

theorem allIx_zero {l : List (List (List Nat))} {f : Nat → List (List Nat) → Bool}
    (h : allIx l f 0 = true) : ∀ i < l.length, f i (l.getD i []) = true := fun i hi => by
  simpa using (allIx_iff l f 0).1 h i hi

theorem add6_lt {t : Nat} (ht : t < 6) : Nat.add 6 t < 28 := by
  change 6 + t < 28
  omega

theorem notB_beq_zero {x : Nat} (h : x ≠ 0) : notB (Nat.beq x 0) = true := by
  cases x with
  | zero => exact absurd rfl h
  | succ n => rfl

@[expose] def elList : List GL6F3 :=
  f5TGens ++ [f5XA, f5XB, f5XM1, f5XM2, f5XM0, f5XA, f5XM0, f5R2, f5R3, f5R4, f5R5, f5R6, f5R7,
    f5R8, f5XM1, f5R10, f5XM2, f5R12, f5XB, f5R14, f5R15]

@[expose] def elG (i : ℕ) : GL6F3 := elList.getD i 1

theorem el_code : ∀ i < 28, matCode 3 6 6 (elG i : Matrix (Fin 6) (Fin 6) (ZMod 3)) = EL i := by
  decide +kernel

theorem elG_lt7 {i : ℕ} (hi : i < 7) : elG i = f5TGens.getD i 1 := by
  interval_cases i <;> rfl

theorem getD_lt7 {i : ℕ} (hi : i < 7) (x : GL6F3) :
    (f5TGens ++ [x]).getD i 1 = elG i := by
  rw [elG_lt7 hi]
  interval_cases i <;> rfl

@[expose] def LL (t : ℕ) : List GL6F3 :=
  [f5TGens, f5GensA, f5GensB, f5GensM1, f5GensM2, f5GensM0].getD t []

@[expose] def memL (t : ℕ) : Subgroup GL6F3 := Subgroup.closure {g | g ∈ LL t}

theorem LL_zero : LL 0 = f5TGens := rfl

theorem LL_pos {t : ℕ} (h0 : 0 < t) (ht : t < 6) : LL t = f5TGens ++ [elG (6 + t)] := by
  interval_cases t <;> rfl

theorem len_LL {t : ℕ} (ht : t < 6) : (LL t).length = lenL t := by
  interval_cases t <;> rfl

theorem len_LL_pos {t : ℕ} (h0 : 0 < t) (ht : t < 6) : (LL t).length = 8 := by
  interval_cases t <;> rfl

theorem LG_code {t : ℕ} (ht : t < 6) :
    ∀ a < (LL t).length,
      LG t a = matCode 3 6 6 ((LL t).getD a 1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  intro a ha
  rcases Nat.lt_or_ge a 7 with h7 | h7
  · have e1 : LG t a = EL a := by
      unfold LG
      rw [Nat.blt_eq.mpr h7]
    have e2 : (LL t).getD a 1 = elG a := by
      rcases Nat.eq_zero_or_pos t with rfl | h0
      · exact (elG_lt7 h7).symm
      · rw [LL_pos h0 ht, getD_lt7 h7]
    rw [e1, e2, el_code a (by omega)]
  · rcases Nat.eq_zero_or_pos t with rfl | h0
    · exact absurd ha (by rw [LL_zero]; exact Nat.not_lt.2 h7)
    · rw [len_LL_pos h0 ht] at ha
      obtain rfl : a = 7 := by omega
      have e1 : LG t 7 = EL (6 + t) := rfl
      rw [e1, LL_pos h0 ht, ← el_code (6 + t) (by omega)]
      rfl

theorem T_le {t : ℕ} (ht : t < 6) : memL 0 ≤ memL t := by
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact le_rfl
  · refine Subgroup.closure_mono fun g hg => ?_
    change g ∈ LL t
    rw [LL_pos h0 ht]
    exact List.mem_append_left _ hg

theorem memL_le {t : ℕ} (ht : t < 6) {L : Subgroup GL6F3} (hT : memL 0 ≤ L)
    (hx : t ≠ 0 → elG (6 + t) ∈ L) : memL t ≤ L := by
  rw [memL, Subgroup.closure_le]
  intro g hg
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact hT (Subgroup.subset_closure hg)
  · change g ∈ LL t at hg
    rw [LL_pos h0 ht] at hg
    rcases List.mem_append.1 hg with h | h
    · exact hT (Subgroup.subset_closure h)
    · rw [List.mem_singleton.1 h]
      exact hx (by omega)

theorem word_memL {t i : ℕ} (ht : t < 6) (hi : i < 28) {w : List ℕ}
    (h : wordAt m6 l6ONE (LG t) (lenL t) w (EL i) = true) : elG i ∈ memL t := by
  rw [← el_code i hi, ← len_LL ht] at h
  exact mem_of_wordAt m6_enc (LL t) (LG_code ht) h

theorem T_code : ∀ j < f5TGens.length,
    EL j = matCode 3 6 6 (f5TGens.getD j 1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  intro j hj
  have hj' : j < 7 := hj
  rw [← elG_lt7 hj', el_code j (by omega)]

theorem T_facts :
    (∀ k < 128, ∃ g ∈ memL 0, matCode 3 6 6 (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = TE k) ∧
      Nat.card (memL 0) = 128 ∧
      ∀ g ∈ memL 0, ∃ k < 128, matCode 3 6 6 (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = TE k := by
  have h := (allN_iff _ _).1 ch7600t
  have ht : ∀ k < 128, treeAt m6 l6ONE EL f5TGens.length TE TP k = true := fun k hk =>
    (andB_eq_true (h k hk)).1
  have hs : ∀ k < 128, sortAt 128 TE TS k = true := fun k hk =>
    (andB_eq_true (andB_eq_true (h k hk)).2).1
  have hc : ∀ k < 128, closedAt m6 EL f5TGens.length 128 TE TC k = true := fun k hk =>
    (andB_eq_true (andB_eq_true (h k hk)).2).2
  obtain ⟨h1, -, h3⟩ := clos_card m6_enc f5TGens T_code (by norm_num) ht hs
  obtain ⟨h4, h5⟩ := h3 hc
  exact ⟨h1, h4, h5⟩

theorem rep_code : ∀ a < 16,
    matCode 3 6 6 (elG (12 + a) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = RC a := fun a ha =>
  el_code (12 + a) (by omega)

theorem UE_zero : Nat.beq (UE 0) l6ONE = true := (andB_eq_true ch7600u).1

theorem U_trans : ∀ i < 405, transAt m6 RC 16 TE 128 UE UR i = true :=
  (allN_iff _ _).1 (andB_eq_true ch7600u).2

theorem U_code :
    ∀ i < 405, ∃ u : GL6F3, matCode 3 6 6 (u : Matrix (Fin 6) (Fin 6) (ZMod 3)) = UE i :=
  fun i hi => by
    obtain ⟨a, -, e, -, he⟩ := trans_sound m6_enc rep_code T_facts.1 U_trans i hi
    exact ⟨_, he⟩

theorem M0_tab : ∀ i < 405, ctabAt m6 (LG 5) (LL 5).length TE 128 UE 405 CR i = true := by
  have h : ∀ c < 5, allR (81 * c) 81
      (ctabAt m6 (LG 5) 8 TE 128 UE 405 CR) = true := by
    intro c hc
    interval_cases c
    · exact ch7600m00
    · exact ch7600m01
    · exact ch7600m02
    · exact ch7600m03
    · exact ch7600m04
  intro i hi
  rw [len_LL_pos (by norm_num) (by norm_num)]
  exact forall_of_chunks 81 5 _ h i (by omega)

theorem M0_cover : ∀ σ ∈ memL 5, ∃ a < 16, ∃ π ∈ memL 0, ∃ κ ∈ memL 0,
    σ = π * elG (12 + a) * κ :=
  ctab_cover m6_enc (LL 5) (LG_code (by norm_num)) rep_code T_facts.1 U_trans (by norm_num)
    UE_zero M0_tab

theorem M0_le : Nat.card (memL 5) ≤ 51840 := by
  have := ctab_card m6_enc (LL 5) (LG_code (by norm_num)) T_facts.1 U_code (by norm_num) UE_zero
    M0_tab
  rwa [T_facts.2.1] at this

theorem mem_tab {t n o : ℕ} (h0 : 0 < t) (ht : t < 6) (h : memOK t n o = true) :
    (∀ i < n, ∃ u : GL6F3,
      matCode 3 6 6 (u : Matrix (Fin 6) (Fin 6) (ZMod 3)) = UE (MJ (Nat.add o i))) ∧
    Nat.beq (UE (MJ (Nat.add o 0))) l6ONE = true ∧
    ∀ i < n, ctabAt m6 (LG t) (LL t).length TE 128 (fun i => UE (MJ (Nat.add o i))) n
      (fun r => CR (Nat.add (Nat.add 3240 (Nat.mul 8 o)) r)) i = true := by
  obtain ⟨hm0, h⟩ := andB_eq_true h
  obtain ⟨hmj, hc⟩ := andB_eq_true h
  refine ⟨fun i hi => U_code _ (Nat.blt_eq.mp ((allN_iff _ _).1 hmj i hi)), ?_, ?_⟩
  · change Nat.beq (UE (MJ o)) l6ONE = true
    rw [Nat.eq_of_beq_eq_true hm0]
    exact UE_zero
  · rw [len_LL_pos h0 ht]
    exact (allN_iff _ _).1 hc

theorem mem_le {t n o : ℕ} (h0 : 0 < t) (ht : t < 6) (hn : 0 < n) (h : memOK t n o = true) :
    Nat.card (memL t) ≤ 128 * n := by
  obtain ⟨hU, h1, hc⟩ := mem_tab h0 ht h
  have := ctab_card m6_enc (LL t) (LG_code ht) T_facts.1 hU hn h1 hc
  rwa [T_facts.2.1] at this

theorem sub_dvd {t N nK oE oC oK : ℕ} (ht : t < 6) (hN : 0 < N)
    (h : subOK t N nK oE oC oK = true) : N ∣ Nat.card (memL t) := by
  obtain ⟨hw, hl⟩ := andB_eq_true h
  have hK : ∀ j < nK, ∃ g ∈ memL t,
      matCode 3 6 6 (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = SK (Nat.add oK j) := by
    intro j hj
    obtain ⟨h1, h2⟩ := andB_eq_true ((allN_iff _ _).1 hw j hj)
    rw [← len_LL ht] at h1
    obtain ⟨g, hg, hge⟩ := wordG_mem m6_enc (LL t) (LG_code ht) h1
    exact ⟨g, hg, hge.trans (Nat.eq_of_beq_eq_true h2)⟩
  have hl' := (allN_iff _ _).1 hl
  exact dvd_card_of_clos m6_enc hK hN (fun k hk => (andB_eq_true (hl' k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).2)

theorem T_dvd {t : ℕ} (ht : t < 6) : 128 ∣ Nat.card (memL t) := by
  rw [← T_facts.2.1]
  exact Subgroup.card_dvd_of_le (T_le ht)

theorem inc_mem (i a b : ℕ) (hi : i < incW.length) (ha : nth (getW (incW.getD i []) 0) 0 = a)
    (hb : nth (getW (incW.getD i []) 0) 1 = b) (hb6 : b < 6) (ha6 : 6 + a < 28) :
    elG (6 + a) ∈ memL b := by
  have h : wordAt m6 l6ONE (LG (nth (getW (incW.getD i []) 0) 1))
      (lenL (nth (getW (incW.getD i []) 0) 1)) (getW (incW.getD i []) 1)
      (EL (Nat.add 6 (nth (getW (incW.getD i []) 0) 0))) = true :=
    allIx_zero ch7600inc i hi
  rw [ha, hb] at h
  exact word_memL hb6 ha6 h

theorem XA_M1 : elG 7 ∈ memL 3 := inc_mem 0 1 3 (by decide) (by decide) (by decide) (by norm_num)
  (by norm_num)

theorem XB_M1 : elG 8 ∈ memL 3 := inc_mem 1 2 3 (by decide) (by decide) (by decide) (by norm_num)
  (by norm_num)

theorem XB_M2 : elG 8 ∈ memL 4 := inc_mem 2 2 4 (by decide) (by decide) (by decide) (by norm_num)
  (by norm_num)

theorem XM1_M0 : elG 9 ∈ memL 5 := inc_mem 3 3 5 (by decide) (by decide) (by decide)
  (by norm_num) (by norm_num)

theorem XM2_M0 : elG 10 ∈ memL 5 := inc_mem 4 4 5 (by decide) (by decide) (by decide)
  (by norm_num) (by norm_num)

theorem XA_not_B : elG 7 ∉ memL 2 := by
  have h := (allN_iff _ _).1 ch7600not
  rw [← el_code 7 (by norm_num)] at h
  obtain ⟨hU, h1, hc⟩ := mem_tab (t := 2) (n := 3) (o := 3) (by norm_num) (by norm_num) ch7600mB
  exact notIn_sound m6_enc T_facts.2.2
    (ctab_sound m6_enc (LL 2) (LG_code (by norm_num)) T_facts.1 hU (by norm_num) h1 hc) h

theorem card_eq {t n : ℕ} (hle : Nat.card (memL t) ≤ n) (hd : n ∣ Nat.card (memL t)) :
    Nat.card (memL t) = n :=
  card_eq_of_dvd_of_le hd hle

theorem dvd_of_lcm {a b c n : ℕ} (h : Nat.lcm a b = c) (ha : a ∣ n) (hb : b ∣ n) : c ∣ n := by
  rw [← h]
  exact Nat.lcm_dvd ha hb

theorem card_A : Nat.card (memL 1) = 384 :=
  card_eq (mem_le (by norm_num) (by norm_num) (by norm_num) ch7600mA)
    (dvd_of_lcm (by decide) (T_dvd (by norm_num)) (sub_dvd (by norm_num) (by norm_num) ch7600sA))

theorem card_B : Nat.card (memL 2) = 384 :=
  card_eq (mem_le (by norm_num) (by norm_num) (by norm_num) ch7600mB)
    (dvd_of_lcm (by decide) (T_dvd (by norm_num)) (sub_dvd (by norm_num) (by norm_num) ch7600sB))

theorem card_M1 : Nat.card (memL 3) = 1152 :=
  card_eq (mem_le (by norm_num) (by norm_num) (by norm_num) ch7600mM1)
    (dvd_of_lcm (by decide) (T_dvd (by norm_num))
      (sub_dvd (by norm_num) (by norm_num) ch7600sM1))

theorem card_M2 : Nat.card (memL 4) = 1920 :=
  card_eq (mem_le (by norm_num) (by norm_num) (by norm_num) ch7600mM2)
    (dvd_of_lcm (a := 384) (b := 5) (by decide)
      (dvd_of_lcm (a := 128) (b := 3) (by decide) (T_dvd (by norm_num))
        (sub_dvd (by norm_num) (by norm_num) ch7600sM2a))
      (sub_dvd (by norm_num) (by norm_num) ch7600sM2b))

theorem M1_le_M0 : memL 3 ≤ memL 5 :=
  memL_le (by norm_num) (T_le (by norm_num)) fun _ => XM1_M0

theorem M2_le_M0 : memL 4 ≤ memL 5 :=
  memL_le (by norm_num) (T_le (by norm_num)) fun _ => XM2_M0

theorem card_M0 : Nat.card (memL 5) = 51840 :=
  card_eq M0_le
    (dvd_of_lcm (a := 5760) (b := 81) (by decide)
      (dvd_of_lcm (a := 1152) (b := 1920) (by decide)
        (card_M1 ▸ Subgroup.card_dvd_of_le M1_le_M0) (card_M2 ▸ Subgroup.card_dvd_of_le M2_le_M0))
      (sub_dvd (by norm_num) (by norm_num) ch7600sM0))

theorem rep_join (j : ℕ) (hj : j < 16) :
    ∃ t < 6, memL 0 ⊔ Subgroup.closure {elG (12 + j)} = memL t := by
  obtain ⟨hl, hall⟩ := andB_eq_true ch7600rep
  have h : repAt j (repW.getD j []) = true :=
    allIx_zero hall j (by rw [Nat.eq_of_beq_eq_true hl]; exact hj)
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨ht6, h⟩ := andB_eq_true h
  obtain ⟨hx, hρ⟩ := andB_eq_true h
  have ht : hd (getW (repW.getD j []) 0) < 6 := Nat.blt_eq.mp ht6
  refine ⟨_, ht, le_antisymm (sup_le (T_le ht) ?_) (memL_le ht le_sup_left fun ht0 => ?_)⟩
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact word_memL (i := 12 + j) ht (by omega) hρ
  · have hw := impB_eq_true hx (notB_beq_zero ht0)
    have hA : ∀ a < (f5TGens ++ [elG (12 + j)]).length, TR j a =
        matCode 3 6 6 ((f5TGens ++ [elG (12 + j)]).getD a 1 :
          Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
      intro a ha
      rcases Nat.lt_or_ge a 7 with h7 | h7
      · have e1 : TR j a = EL a := by
          unfold TR
          rw [Nat.blt_eq.mpr h7]
        rw [e1, getD_lt7 h7, el_code a (by omega)]
      · have ha8 : a < 8 := ha
        obtain rfl : a = 7 := by omega
        have e1 : TR j 7 = EL (12 + j) := rfl
        rw [e1, ← el_code (12 + j) (by omega)]
        rfl
    rw [← el_code _ (add6_lt ht)] at hw
    have hm := mem_of_wordAt m6_enc (f5TGens ++ [elG (12 + j)]) hA hw
    refine (Subgroup.closure_le _).2 (fun g hg => ?_) hm
    rcases List.mem_append.1 hg with h | h
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
    · rw [List.mem_singleton.1 h]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

theorem LGG_code {a b : ℕ} (ha : a < 6) (hb : b < 6) :
    ∀ l < (LL a ++ LL b).length, LGG a b l =
      matCode 3 6 6 ((LL a ++ LL b).getD l 1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  intro l hl
  rw [List.length_append] at hl
  rcases Nat.lt_or_ge l (lenL a) with h1 | h1
  · have e1 : LGG a b l = LG a l := by
      unfold LGG
      rw [Nat.blt_eq.mpr h1]
    rw [e1, List.getD_append _ _ _ _ (by rw [len_LL ha]; exact h1)]
    exact LG_code ha l (by rw [len_LL ha]; exact h1)
  · have hf : Nat.blt l (lenL a) = false := by
      cases h : Nat.blt l (lenL a)
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt.2 h1)
    have e1 : LGG a b l = LG b (l - lenL a) := by
      unfold LGG
      rw [hf]
      rfl
    rw [e1, List.getD_append_right _ _ _ _ (by rw [len_LL ha]; exact h1), len_LL ha]
    exact LG_code hb _ (by rw [len_LL ha] at hl; omega)

theorem join_eq (a b : ℕ) (ha : a < 6) (hb : b < 6) : ∃ c < 6, memL a ⊔ memL b = memL c := by
  obtain ⟨hj1, hj2⟩ := andB_eq_true ch7600join
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
    · intro h; exact absurd h (by decide)
    · intro _; rfl
  obtain ⟨ea, eb⟩ := andB_eq_true hab
  have h : joinAt (joinW.getD i []) = true := allIx_zero hj1 i hi
  unfold joinAt at h
  rw [letB_eq, letB_eq, letB_eq, Nat.eq_of_beq_eq_true ea, Nat.eq_of_beq_eq_true eb] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨hc6, h⟩ := andB_eq_true h
  obtain ⟨hxc, h⟩ := andB_eq_true h
  obtain ⟨hxa, hxb⟩ := andB_eq_true h
  have hc : nth (getW (joinW.getD i []) 0) 2 < 6 := Nat.blt_eq.mp hc6
  refine ⟨_, hc, le_antisymm (sup_le
    (memL_le ha (T_le hc) fun h0 =>
      word_memL hc (add6_lt ha) (impB_eq_true hxa (notB_beq_zero h0)))
    (memL_le hb (T_le hc) fun h0 =>
      word_memL hc (add6_lt hb) (impB_eq_true hxb (notB_beq_zero h0))))
    (memL_le hc ((T_le ha).trans le_sup_left) fun h0 => ?_)⟩
  have hw := impB_eq_true hxc (notB_beq_zero h0)
  have hlen : Nat.add (lenL a) (lenL b) = (LL a ++ LL b).length := by
    rw [List.length_append, len_LL ha, len_LL hb]
    rfl
  rw [← el_code _ (add6_lt hc), hlen] at hw
  have hm := mem_of_wordAt m6_enc (LL a ++ LL b) (LGG_code ha hb) hw
  refine (Subgroup.closure_le _).2 (fun g hg => ?_) hm
  rcases List.mem_append.1 hg with h | h
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure h)

theorem overgroups : ∀ Z : Subgroup GL6F3, memL 0 ≤ Z → Z ≤ memL 5 → ∃ i < 6, memL i = Z :=
  lat_overgroups_of (Q := memL) (ρ := fun j => elG (12 + j)) (by norm_num : 0 < 6) rfl
    (fun i hi => T_le hi) M0_cover rep_join fun a ha b hb => join_eq a b ha hb

theorem facts :
    Nat.card (Subgroup.closure {g | g ∈ f5TGens}) = 128 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensA}) = 384 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensB}) = 384 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM1}) = 1152 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM2}) = 1920 ∧
    Nat.card (Subgroup.closure {g | g ∈ f5GensM0}) = 51840 ∧
    (∀ Y : Subgroup GL6F3, Subgroup.closure {g | g ∈ f5TGens} ≤ Y →
      Y ≤ Subgroup.closure {g | g ∈ f5GensM0} →
      Y = Subgroup.closure {g | g ∈ f5TGens} ∨ Y = Subgroup.closure {g | g ∈ f5GensA} ∨
      Y = Subgroup.closure {g | g ∈ f5GensB} ∨ Y = Subgroup.closure {g | g ∈ f5GensM1} ∨
      Y = Subgroup.closure {g | g ∈ f5GensM2} ∨ Y = Subgroup.closure {g | g ∈ f5GensM0}) ∧
    f5XA ∈ Subgroup.closure {g | g ∈ f5GensM1} ∧ f5XB ∈ Subgroup.closure {g | g ∈ f5GensM1} ∧
    f5XB ∈ Subgroup.closure {g | g ∈ f5GensM2} ∧ f5XM1 ∈ Subgroup.closure {g | g ∈ f5GensM0} ∧
    f5XM2 ∈ Subgroup.closure {g | g ∈ f5GensM0} ∧ f5XA ∉ Subgroup.closure {g | g ∈ f5GensB} := by
  refine ⟨T_facts.2.1, card_A, card_B, card_M1, card_M2, card_M0, fun Y hTY hYM => ?_, XA_M1,
    XB_M1, XB_M2, XM1_M0, XM2_M0, XA_not_B⟩
  obtain ⟨i, hi, hQ⟩ := overgroups Y hTY hYM
  interval_cases i
  · exact Or.inl hQ.symm
  · exact Or.inr (Or.inl hQ.symm)
  · exact Or.inr (Or.inr (Or.inl hQ.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hQ.symm)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ.symm))))

end CertificateChecks.KernelSimsF5

end
