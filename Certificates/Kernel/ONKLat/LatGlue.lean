module

public import Certificates.Kernel.ONKLat.LatChecks
public import Certificates.Kernel.ONKLat.SelGlue
public import CFSG.Certificates.Kernel.CosetLat.Sound

public section

namespace CertificateChecks.KernelONKLat.Glue

open Equiv CFSG.KC.CosetLat CFSG.KC.Misc.ClosW CertificateChecks.KernelONKLat CFSG.ONSchreier
  CFSG.KC.LQT.P CFSG.KS.PEnum
open CFSG.KC.Misc.Clos (ClosEnc clos_card treeAt sortAt closedAt letB_eq allN_iff andB_eq_true
  allR_iff forall_of_chunks)

@[expose] def cl (L : List (Perm (Fin 120))) : Subgroup (Perm (Fin 120)) :=
  Subgroup.closure {g | g ∈ L}

@[expose] noncomputable def mGens : List (Perm (Fin 120)) :=
  [permOfArr 120 Data.M120Chain.generators[0]!, permOfArr 120 Data.M120Chain.generators[1]!]

theorem henc : ClosEnc (wcode (n := 120) 7) m120 one120 := CertificateChecks.KernelSpor.ONKL.henc120

theorem mg_eq : ∀ j < 2, MG j = CertificateChecks.KernelSpor.ON5M.G j := by decide +kernel

theorem code_mGen {j : ℕ} (hj : j < 2) :
    wcode 7 (permOfArr 120 Data.M120Chain.generators[j]!) = CertificateChecks.KernelSpor.ON5M.G j := by
  have hk : CertificateChecks.KernelSpor.ON5M.k = 2 := rfl
  obtain ⟨e, hc⟩ := (gensOK_of CertificateChecks.KernelSpor.ON5K.m_gens).2 j (by rw [hk]; exact hj)
  have hp := prep_smallGen small_chain_certs.2.1 j (by rw [m120_gens_size]; exact hj)
  have hp' : PRep 120 (CFSG.KS.Raw.unpack 120 7 (CertificateChecks.KernelSpor.ON5M.G j))
      (permOfArr 120 Data.M120Chain.generators[j]!) := fun x => by
    rw [← e]
    exact hp x
  exact CertificateChecks.KernelSpor.ONKL.wcode_of_prep (by norm_num)
    (CertificateChecks.KernelSpor.ONKL.shr_of_canon hc) hp'

theorem hMG : ∀ j < mGens.length, MG j = wcode 7 (mGens.getD j 1) := by
  intro j hj
  have hj2 : j < 2 := hj
  rw [mg_eq j hj2]
  interval_cases j
  · exact (code_mGen (by norm_num)).symm
  · exact (code_mGen (by norm_num)).symm

theorem cl_mGens : cl mGens = onM120Chain.originalSubgroup := by
  rw [onM120Chain, smallChain_sub, m120_gens_size, cl]
  congr 1
  ext g
  simp only [mGens, List.mem_cons, Set.mem_setOf_eq, Set.mem_image, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem getD_mem_cl (L : List (Perm (Fin 120))) {j : ℕ} (hj : j < L.length) : L.getD j 1 ∈ cl L :=
  getD_mem_closure L hj

theorem of_wordAt (gens : List (Perm (Fin 120))) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = wcode 7 (gens.getD a 1)) {w : List ℕ} {c : ℕ}
    (h : wordAt m120 one120 A gens.length w c = true) : ∃ g ∈ cl gens, wcode 7 g = c := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨g, hg, hge⟩ := wordG_mem henc gens hA h1
  exact ⟨g, hg, hge.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem of_wordsAt (gens : List (Perm (Fin 120))) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = wcode 7 (gens.getD a 1)) {ws : List (List ℕ)} {o n : ℕ}
    {G : ℕ → ℕ} (h : wordsAt A gens.length ws o G n = true) :
    ∀ k < n, ∃ g ∈ cl gens, wcode 7 g = G k :=
  fun k hk => of_wordAt gens hA ((allN_iff _ _).1 h k hk)

theorem mem_of_code {X : List (Perm (Fin 120))} {x : Perm (Fin 120)}
    (h : ∃ g ∈ cl X, wcode 7 g = wcode 7 x) : x ∈ cl X := by
  obtain ⟨g, hg, he⟩ := h
  rwa [henc.inj he] at hg

theorem cl_le_of_codes {L X : List (Perm (Fin 120))} {G : ℕ → ℕ}
    (hG : ∀ k < L.length, G k = wcode 7 (L.getD k 1))
    (h : ∀ k < L.length, ∃ g ∈ cl X, wcode 7 g = G k) : cl L ≤ cl X := by
  rw [cl, Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  have e : L.getD k 1 = L[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [← e]
  obtain ⟨g, hg, hge⟩ := h k hk
  exact mem_of_code ⟨g, hg, hge.trans (hG k hk)⟩

theorem cl_append (L L' : List (Perm (Fin 120))) : cl (L ++ L') = cl L ⊔ cl L' := by
  rw [cl, cl, cl, ← Subgroup.closure_union]
  congr 1
  ext x
  simp

theorem allIx_get {l : List (List (List ℕ))} {f : ℕ → List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, allIx l f i₀ = true → ∀ i < l.length, f (i₀ + i) (l.getD i []) = true := by
  induction l with
  | nil => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    intro i₀ h i hi
    obtain ⟨h1, h2⟩ := andB_eq_true h
    cases i with
    | zero => exact h1
    | succ i =>
      have := ih h2 i (by simpa using hi)
      have e : i₀ + (i + 1) = Nat.succ i₀ + i := by omega
      rw [e]
      exact this

theorem allIx_mem {l : List (List (List ℕ))} {f : List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, allIx l (fun _ e => f e) i₀ = true → ∀ e ∈ l, f e = true := by
  induction l with
  | nil => intro _ _ e he; exact absurd he List.not_mem_nil
  | cons x xs ih =>
    intro i₀ h e he
    obtain ⟨h1, h2⟩ := andB_eq_true h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact ih h2 e he

theorem exists_of_notB_allIx {l : List (List (List ℕ))} {P : List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, CFSG.KC.Ord.notB (allIx l (fun _ e => CFSG.KC.Ord.notB (P e)) i₀) = true →
      ∃ e ∈ l, P e = true := by
  induction l with
  | nil => intro _ h; exact absurd h Bool.false_ne_true
  | cons x xs ih =>
    intro i₀ h
    cases hx : P x
    · have h' : CFSG.KC.Ord.notB (allIx xs (fun _ e => CFSG.KC.Ord.notB (P e)) (Nat.succ i₀)) =
          true := by
        have e : allIx (x :: xs) (fun _ e => CFSG.KC.Ord.notB (P e)) i₀ =
            CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (P x))
              (allIx xs (fun _ e => CFSG.KC.Ord.notB (P e)) (Nat.succ i₀)) := rfl
        rw [e, hx] at h
        exact h
      obtain ⟨e, he, hPe⟩ := ih h'
      exact ⟨e, List.mem_cons_of_mem _ he, hPe⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

theorem joinW_len : joinW.length = 9 := by decide +kernel

theorem joinAt_of {i : ℕ} (hi : i < 9) : joinAt (joinW.getD i []) = true := by
  have h := allIx_get (andB_eq_true ch812105join).1 i (by rw [joinW_len]; exact hi)
  exact h

theorem join_words_R {i a o : ℕ} (hi : i < 9)
    (habc : getW (joinW.getD i []) 0 = [a, 2, 2]) (ho : o = 3) (hla : lenL a = 3) :
    ∀ k < 3, ∃ g ∈ cl mGens, wcode 7 g = LG a k := by
  have h := joinAt_of hi
  unfold joinAt at h
  rw [letB_eq, letB_eq, letB_eq, habc] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨hw, -⟩ := andB_eq_true h
  have hw2 : wordsAt (LG 2) mGens.length (joinW.getD i []) 3 (LG a) (lenL a) = true := hw
  have hw' : wordsAt (LG 2) mGens.length (joinW.getD i []) 3 (LG a) 3 = true := by
    rw [hla] at hw2
    exact hw2
  have hLG : ∀ j < mGens.length, LG 2 j = wcode 7 (mGens.getD j 1) := fun j hj => hMG j hj
  subst ho
  exact of_wordsAt mGens hLG hw'

theorem join2 : getW (joinW.getD 2 []) 0 = [0, 2, 2] := by decide +kernel

theorem join5 : getW (joinW.getD 5 []) 0 = [1, 2, 2] := by decide +kernel

theorem tGen_ex : ∀ k < 3, ∃ g ∈ cl mGens, wcode 7 g = LG 0 k :=
  join_words_R (i := 2) (by norm_num) join2 rfl rfl

theorem hGen_ex : ∀ k < 3, ∃ g ∈ cl mGens, wcode 7 g = LG 1 k :=
  join_words_R (i := 5) (by norm_num) join5 rfl rfl

open scoped Classical in
noncomputable def gen (t k : ℕ) : Perm (Fin 120) :=
  if h : ∃ g ∈ onM120Chain.originalSubgroup, wcode 7 g = LG t k then h.choose else 1

theorem gen_spec {t k : ℕ} (ht : t < 2) (hk : k < 3) :
    gen t k ∈ cl mGens ∧ wcode 7 (gen t k) = LG t k := by
  have hex : ∃ g ∈ onM120Chain.originalSubgroup, wcode 7 g = LG t k := by
    rw [← cl_mGens]
    interval_cases t
    · exact tGen_ex k hk
    · exact hGen_ex k hk
  rw [gen, dif_pos hex, cl_mGens]
  exact hex.choose_spec

@[expose] noncomputable def Lgens (t : ℕ) : List (Perm (Fin 120)) :=
  if t = 0 then [gen 0 0, gen 0 1, gen 0 2] else if t = 1 then [gen 1 0, gen 1 1, gen 1 2]
  else mGens

@[expose] noncomputable def Lm (t : ℕ) : Subgroup (Perm (Fin 120)) := cl (Lgens t)

@[expose] noncomputable def tGens : List (Perm (Fin 120)) := Lgens 0

theorem Lgens_zero : Lgens 0 = [gen 0 0, gen 0 1, gen 0 2] := by
  rw [Lgens, if_pos rfl]

theorem Lgens_one : Lgens 1 = [gen 1 0, gen 1 1, gen 1 2] := by
  rw [Lgens, if_neg (by norm_num), if_pos rfl]

theorem Lgens_two : Lgens 2 = mGens := by
  rw [Lgens, if_neg (by norm_num), if_neg (by norm_num)]

theorem lenL_zero : lenL 0 = 3 := rfl

theorem lenL_one : lenL 1 = 3 := rfl

theorem lenL_two : lenL 2 = 2 := rfl

theorem gens3 {t : ℕ} (ht : t < 2) :
    ∀ j < 3, LG t j = wcode 7 ([gen t 0, gen t 1, gen t 2].getD j 1) := by
  intro j hj
  interval_cases j
  · rw [List.getD_cons_zero]
    exact (gen_spec ht (by norm_num)).2.symm
  · rw [List.getD_cons_succ, List.getD_cons_zero]
    exact (gen_spec ht (by norm_num)).2.symm
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
    exact (gen_spec ht (by norm_num)).2.symm

theorem bridgeL {t : ℕ} (ht : t < 3) : (Lgens t).length = lenL t ∧
    ∀ j < lenL t, LG t j = wcode 7 ((Lgens t).getD j 1) := by
  interval_cases t
  · rw [Lgens_zero, lenL_zero]
    exact ⟨rfl, gens3 (by norm_num)⟩
  · rw [Lgens_one, lenL_one]
    exact ⟨rfl, gens3 (by norm_num)⟩
  · rw [Lgens_two, lenL_two]
    exact ⟨rfl, fun j hj => hMG j hj⟩

theorem hGL {t : ℕ} (ht : t < 3) :
    ∀ j < (Lgens t).length, LG t j = wcode 7 ((Lgens t).getD j 1) :=
  fun j hj => (bridgeL ht).2 j (by rw [← (bridgeL ht).1]; exact hj)

theorem hGT : ∀ j < tGens.length, EL j = wcode 7 (tGens.getD j 1) :=
  fun j hj => hGL (t := 0) (by norm_num) j hj

theorem Lm_le_R {t : ℕ} (ht : t < 3) : Lm t ≤ cl mGens := by
  refine cl_le_of_codes (hGL ht) fun k hk => ?_
  rw [(bridgeL ht).1] at hk
  interval_cases t
  · exact tGen_ex k hk
  · exact hGen_ex k hk
  · exact ⟨_, getD_mem_cl mGens hk, (hMG k hk).symm⟩

theorem Lm_two : Lm 2 = cl mGens := by rw [Lm, Lgens_two]

theorem tTree :
    ∀ k < 128, treeAt m120 one120 EL tGens.length TE TP k = true :=
  fun k hk => (andB_eq_true ((allN_iff _ _).1 ch812105t k hk)).1

theorem tParts :
    (∀ k < 128, ∃ g ∈ cl tGens, wcode 7 g = TE k) ∧ Nat.card (cl tGens) = 128 := by
  have h := clos_card henc tGens (G := EL) (N := 128) (E := TE) (PA := TP) (SG := TS) hGT
    (by norm_num) tTree
    (fun k hk => (andB_eq_true (andB_eq_true ((allN_iff _ _).1 ch812105t k hk)).2).1)
  exact ⟨h.1, (h.2.2 (CT := TC)
    (fun k hk => (andB_eq_true (andB_eq_true ((allN_iff _ _).1 ch812105t k hk)).2).2)).1⟩

theorem hT : ∀ k < 128, ∃ g ∈ cl tGens, wcode 7 g = TE k :=
  tParts.1

theorem card_T : Nat.card (cl tGens) = 128 := tParts.2

theorem rep_ex : ∀ a < 10, ∃ g ∈ cl mGens, wcode 7 g = RC a := by
  have h : wordsAt MG mGens.length repM 0 RC 10 = true := ch812105repM
  exact of_wordsAt mGens hMG h

open scoped Classical in
noncomputable def ρ (a : ℕ) : Perm (Fin 120) :=
  if h : ∃ g ∈ onM120Chain.originalSubgroup, wcode 7 g = RC a then h.choose else 1

theorem ρ_code : ∀ a < 10, wcode 7 (ρ a) = RC a := fun a ha => by
  have hex : ∃ g ∈ onM120Chain.originalSubgroup, wcode 7 g = RC a := by
    rw [← cl_mGens]
    exact rep_ex a ha
  rw [ρ, dif_pos hex]
  exact hex.choose_spec.2

theorem hUE0 : Nat.beq (UE 0) one120 = true := (andB_eq_true ch812105u).1

theorem hTrans : ∀ i < 315, transAt m120 RC 10 TE 128 UE UR i = true :=
  fun i hi => (allN_iff _ _).1 (andB_eq_true ch812105u).2 i hi

theorem hCM :
    ∀ i < 315, ctabAt m120 MG mGens.length TE 128 UE 315 CR i = true := by
  have h := forall_of_chunks 105 3 (ctabAt m120 MG 2 TE 128 UE 315 CR) (fun c hc => by
    interval_cases c
    · exact ch812105m0
    · exact ch812105m1
    · exact ch812105m2)
  exact fun i hi => h i (by omega)

theorem getD_append_codes {a b : ℕ} (ha : a < 3) (hb : b < 3) :
    ∀ l < (Lgens a ++ Lgens b).length, LGG a b l = wcode 7 ((Lgens a ++ Lgens b).getD l 1) := by
  intro l hl
  unfold LGG
  by_cases h : l < lenL a
  · rw [Nat.blt_eq.mpr h]
    have h' : l < (Lgens a).length := by rw [(bridgeL ha).1]; exact h
    rw [List.getD_append _ _ _ _ h']
    exact hGL ha l h'
  · have hf : Nat.blt l (lenL a) = false := by
      cases e : Nat.blt l (lenL a)
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hf]
    have h' : (Lgens a).length ≤ l := by rw [(bridgeL ha).1]; omega
    rw [List.getD_append_right _ _ _ _ h', (bridgeL ha).1]
    rw [List.length_append, (bridgeL ha).1] at hl
    exact hGL hb (l - lenL a) (by omega)

theorem join_rec {e : List (List ℕ)} (h : joinAt e = true)
    {a b : ℕ} (hea : nth (getW e 0) 0 = a) (heb : nth (getW e 0) 1 = b) :
    a < 3 ∧ b < 3 ∧ nth (getW e 0) 2 < 3 ∧ Lm a ⊔ Lm b = Lm (nth (getW e 0) 2) := by
  unfold joinAt at h
  rw [letB_eq, letB_eq, letB_eq, hea, heb] at h
  obtain ⟨ha', h⟩ := andB_eq_true h
  obtain ⟨hb', h⟩ := andB_eq_true h
  obtain ⟨hc', h⟩ := andB_eq_true h
  obtain ⟨hw1, h⟩ := andB_eq_true h
  obtain ⟨hw2, hw3⟩ := andB_eq_true h
  have ha : a < 3 := Nat.blt_eq.mp ha'
  have hb : b < 3 := Nat.blt_eq.mp hb'
  set c := nth (getW e 0) 2
  have hc3 : c < 3 := Nat.blt_eq.mp hc'
  have hlen : (Lgens a ++ Lgens b).length = Nat.add (lenL a) (lenL b) := by
    rw [List.length_append, (bridgeL ha).1, (bridgeL hb).1]
    rfl
  rw [← hlen, ← (bridgeL hc3).1] at hw1
  rw [← (bridgeL hc3).1] at hw2 hw3
  rw [← (bridgeL ha).1] at hw2
  rw [← (bridgeL hb).1] at hw3
  refine ⟨ha, hb, hc3, le_antisymm ?_ ?_⟩
  · exact sup_le (cl_le_of_codes (hGL ha) (of_wordsAt (Lgens c) (hGL hc3) hw2))
      (cl_le_of_codes (hGL hb) (of_wordsAt (Lgens c) (hGL hc3) hw3))
  · unfold Lm
    rw [← cl_append]
    exact cl_le_of_codes (hGL hc3) (of_wordsAt _ (getD_append_codes ha hb) hw1)

theorem join_eq :
    ∀ a < 3, ∀ b < 3, ∃ c < 3, Lm a ⊔ Lm b = Lm c := by
  intro a ha b hb
  obtain ⟨hall, hcov⟩ := andB_eq_true ch812105join
  have hc := (allN_iff _ _).1 ((allN_iff _ _).1 hcov a ha) b hb
  obtain ⟨e, he, hP⟩ := exists_of_notB_allIx hc
  obtain ⟨hea, heb⟩ := andB_eq_true hP
  obtain ⟨-, -, hc3, hj⟩ := join_rec (allIx_mem hall e he) (Nat.eq_of_beq_eq_true hea)
    (Nat.eq_of_beq_eq_true heb)
  exact ⟨_, hc3, hj⟩

theorem join1 : nth (getW (joinW.getD 1 []) 0) 0 = 0 ∧ nth (getW (joinW.getD 1 []) 0) 1 = 1 ∧
    nth (getW (joinW.getD 1 []) 0) 2 = 1 := by decide +kernel

theorem T_le {t : ℕ} (ht : t < 3) : cl tGens ≤ Lm t := by
  interval_cases t
  · exact le_rfl
  · obtain ⟨-, -, -, hj⟩ := join_rec (joinAt_of (i := 1) (by norm_num)) join1.1 join1.2.1
    rw [join1.2.2] at hj
    rw [← hj]
    exact le_sup_left
  · rw [Lm_two]
    exact Lm_le_R (t := 0) (by norm_num)

theorem cover :
    ∀ σ ∈ cl mGens, ∃ a < 10, ∃ π ∈ cl tGens, ∃ κ ∈ cl tGens, σ = π * ρ a * κ :=
  ctab_cover henc mGens hMG ρ_code hT hTrans (by norm_num) hUE0 hCM

theorem rep_join :
    ∀ j < 10, ∃ t < 3, cl tGens ⊔ Subgroup.closure {ρ j} = Lm t := by
  intro j hj
  obtain ⟨hl0, h⟩ := andB_eq_true ch812105rep
  have hl : repW.length = 10 := Nat.eq_of_beq_eq_true hl0
  have h := allIx_get h j (by rw [hl]; exact hj)
  rw [Nat.zero_add] at h
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨ht, h⟩ := andB_eq_true h
  obtain ⟨hr, hw⟩ := andB_eq_true h
  set t := hd (getW (repW.getD j []) 0)
  have ht' : t < 3 := Nat.blt_eq.mp ht
  rw [← (bridgeL ht').1] at hr hw
  refine ⟨t, ht', ?_⟩
  have hsup : cl tGens ⊔ Subgroup.closure {ρ j} = cl (tGens ++ [ρ j]) := by
    rw [cl_append]
    congr 1
    rw [cl]
    congr 1
    ext x
    simp
  rw [hsup]
  have hA : ∀ a < (tGens ++ [ρ j]).length, TR j a = wcode 7 ((tGens ++ [ρ j]).getD a 1) := by
    intro a ha
    have hl3 : tGens.length = 3 := by rw [tGens, Lgens_zero]; rfl
    rw [List.length_append, hl3] at ha
    by_cases h3 : a < 3
    · have e : TR j a = EL a := by
        unfold TR
        rw [Nat.blt_eq.mpr h3]
      rw [e, List.getD_append _ _ _ _ (by rw [hl3]; exact h3)]
      exact hGT a (by rw [hl3]; exact h3)
    · have ha3 : a = 3 := by simp at ha; omega
      subst ha3
      have e : TR j 3 = RC j := rfl
      rw [e, List.getD_append_right _ _ _ _ (by rw [hl3]), hl3, Nat.sub_self,
        List.getD_cons_zero]
      exact (ρ_code j hj).symm
  refine le_antisymm ?_ (cl_le_of_codes (hGL ht') (of_wordsAt (tGens ++ [ρ j]) hA hw))
  rw [cl_append]
  refine sup_le (T_le ht') ?_
  rw [cl, Subgroup.closure_le]
  intro x hx
  have hx' : x = ρ j := by simpa using hx
  rw [hx']
  exact mem_of_code ((of_wordAt (Lgens t) (hGL ht') hr).imp fun g hg => ⟨hg.1, hg.2.trans
    (ρ_code j hj).symm⟩)

theorem overgroups : ∀ Y : Subgroup (Perm (Fin 120)),
    cl tGens ≤ Y → Y ≤ cl mGens → ∃ j < 3, Y = Lm j := by
  intro Y h1 h2
  obtain ⟨i, hi, he⟩ := lat_overgroups_of (B := cl tGens) (Mt := cl mGens) (Q := Lm) (nM := 3)
    (nR := 10) (ρ := ρ) (i₀ := 0) (by norm_num) rfl (fun i hi => T_le hi) cover rep_join join_eq
    Y h1 h2
  exact ⟨i, hi, he.symm⟩

theorem three_dvd_Lm {t : ℕ} (ht1 : 1 ≤ t) (ht : t < 3) :
    3 ∣ Nat.card (Lm t) := by
  obtain ⟨hw, h⟩ := andB_eq_true ch812105h3
  obtain ⟨h3, hne⟩ := andB_eq_true h
  have hw' : wordAt m120 one120 (LG 1) (Lgens 1).length h3W (EL 18) = true := hw
  obtain ⟨g, hg, hgc⟩ := of_wordAt (Lgens 1) (hGL (by norm_num)) hw'
  have hg3 : g ^ 3 = 1 := by
    apply henc.inj
    have e3 : g ^ 3 = g * (g * g) := by rw [pow_succ', pow_succ', pow_one]
    rw [henc.enc_one, e3, henc.enc_mul, henc.enc_mul, hgc]
    exact Nat.eq_of_beq_eq_true h3
  have hg1 : g ≠ 1 := fun h => by
    cases hb : Nat.beq (EL 18) one120
    · have he : EL 18 = one120 := by
        rw [← hgc, h]
        exact henc.enc_one
      exact Nat.ne_of_beq_eq_false hb he
    · rw [hb] at hne
      exact absurd hne (by decide)
  have ht12 : t = 1 ∨ t = 2 := by omega
  have hgt : g ∈ Lm t := by
    rcases ht12 with rfl | rfl
    · exact hg
    · exact Lm_le_R (by norm_num) hg
  have ho : orderOf (⟨g, hgt⟩ : Lm t) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg3 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem card_R :
    Nat.card onM120Chain.originalSubgroup = 40320 := by
  rw [m120_enumerates.card, Array.length_toList, CertificateChecks.KernelSpor.ONKL.m120_size]

theorem S₀_le_R : cl tGens ≤ onM120Chain.originalSubgroup := by
  rw [← cl_mGens]
  exact Lm_le_R (t := 0) (by norm_num)

noncomputable abbrev S₀R : Subgroup ↥onM120Chain.originalSubgroup :=
  (cl tGens).subgroupOf onM120Chain.originalSubgroup

theorem card_S₀R : Nat.card S₀R = 2 ^ 7 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S₀_le_R).toEquiv, card_T]
  norm_num

theorem index_S₀R :
    ¬ 2 ∣ S₀R.index := by
  have hi := Subgroup.card_mul_index S₀R
  rw [card_S₀R, card_R] at hi
  have h315 : S₀R.index = 315 := by omega
  rw [h315]
  decide

theorem three_dvd_over_S₀
    (J : Subgroup ↥onM120Chain.originalSubgroup) (hJ : S₀R ≤ J) (hne : J ≠ S₀R) :
    3 ∣ Nat.card J := by
  have hS : cl tGens ≤ J.map onM120Chain.originalSubgroup.subtype := by
    intro x hx
    have hxR : x ∈ onM120Chain.originalSubgroup := S₀_le_R hx
    have hxS : (⟨x, hxR⟩ : ↥onM120Chain.originalSubgroup) ∈ S₀R := Subgroup.mem_subgroupOf.2 hx
    exact ⟨⟨x, hxR⟩, hJ hxS, rfl⟩
  have hR : J.map onM120Chain.originalSubgroup.subtype ≤ cl mGens := by
    rw [cl_mGens]
    exact Subgroup.map_subtype_le J
  obtain ⟨j, hj, hY⟩ := overgroups _ hS hR
  have hcard : Nat.card J = Nat.card (Lm j) := by
    rw [← hY, Subgroup.card_map_of_injective onM120Chain.originalSubgroup.subtype_injective]
  rw [hcard]
  have hj01 : j = 0 ∨ 1 ≤ j := by omega
  rcases hj01 with rfl | h1
  · exfalso
    apply hne
    apply Subgroup.map_injective onM120Chain.originalSubgroup.subtype_injective
    exact hY.trans (Subgroup.map_subgroupOf_eq_of_le S₀_le_R).symm
  · exact three_dvd_Lm h1 hj

theorem three_dvd_over :
    ∀ (P : Sylow 2 ↥onM120Chain.originalSubgroup) (J : Subgroup ↥onM120Chain.originalSubgroup),
      (P : Subgroup ↥onM120Chain.originalSubgroup) ≤ J →
        J ≠ P → 3 ∣ Nat.card J := by
  intro P J hPJ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 ↥onM120Chain.originalSubgroup :=
    (IsPGroup.of_card card_S₀R).toSylow index_S₀R
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥onM120Chain.originalSubgroup) Q P
  have h := congrArg (fun T : Sylow 2 ↥onM120Chain.originalSubgroup =>
    (T : Subgroup ↥onM120Chain.originalSubgroup)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have hQ : (Q : Subgroup ↥onM120Chain.originalSubgroup) = S₀R := rfl
  set e := MulAut.conj g
  have hmap : S₀R.map e.toMonoidHom = (P : Subgroup ↥onM120Chain.originalSubgroup) := by
    rw [← hQ]
    exact h
  have hTe : (P : Subgroup ↥onM120Chain.originalSubgroup).map e.symm.toMonoidHom = S₀R := by
    rw [← hmap, Subgroup.map_map]
    ext x
    simp
  have hJ : S₀R ≤ J.map e.symm.toMonoidHom := by
    rw [← hTe]
    exact Subgroup.map_mono hPJ
  have hne' : J.map e.symm.toMonoidHom ≠ S₀R := fun h' =>
    hne (Subgroup.map_injective e.symm.injective (h'.trans hTe.symm))
  have := three_dvd_over_S₀ _ hJ hne'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

end CertificateChecks.KernelONKLat.Glue

end
