module

public import Certificates.Kernel.Fi23U3.Dce.Facts
public import Certificates.Kernel.Fi23U3.Dce.CoverTabs
public import Certificates.Kernel.Fi23U3.Dce.Cover0
public import Certificates.Kernel.Fi23U3.Dce.Cover1
public import Certificates.Kernel.Fi23U3.Dce.Cover2
public import Certificates.Kernel.Fi23U3.Dce.Cover3
public import Certificates.Kernel.Fi23U3.Dce.Cover4
public import Certificates.Kernel.Fi23U3.Dce.Cover5
public import Certificates.Kernel.Fi23U3.Dce.Chain
public import CFSG.Certificates.Kernel.TwistDce2.ChainSound
public import CFSG.Certificates.Kernel.TwistDce3.TupleSound
public import CFSG.Certificates.Kernel.TwistDce.Cover

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce2 CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration CFSG.KC.YModel
open CFSG.Certificates.TwDce2 (chainB_sound chainLens)
open CFSG.Certificates.TwDce2.Words (kandB_iff)
open CFSG.KC.LaneChain (getN getL colDat)

@[expose] noncomputable def recBool (r : ℕ) : Bool :=
  (wList (RW r)).all (fun c => decide (c < 12)) &&
    (wList (wInv INVM (RW r)) == (wList (RW r)).reverse.map (ivL INVM))

theorem rec_bool : (List.range 44010).all recBool = true := by
  quickRfl

theorem rec_ok : ∀ r < 44010, (∀ c ∈ wList (RW r), c < 12) ∧
    wList (wInv INVM (RW r)) = (wList (RW r)).reverse.map (ivL INVM) := by
  intro r hr
  have h := List.all_eq_true.1 rec_bool r (List.mem_range.2 hr)
  simpa only [recBool, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] using h

set_option maxRecDepth 100000 in
theorem gens_ok : ∀ i < 34, ∀ c ∈ getL CG i, wBelow 12 (gWord INVM RW c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem lens_ok : ∀ i < 34, ∀ m ∈ chainLens ((gRegs INVM RW (getL CG i)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW i), m < 2 ^ 32 := by
  decide +kernel

theorem base_ok : (∀ i < NB, CFSG.KC.TwDce.fld BS (16 * i) 65535 < 54) ∧
    ∀ b ∈ getLL CB 0, ∃ i < NB, colDat 11 b / 2 = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem ds_mem : ∀ d ∈ DS, ∃ j < 34, getN DS j = d := by
  rw [ds_eq.1]
  decide

theorem ds0 : getN DS 0 = 0 := by rw [ds_eq.1]; rfl

theorem cn0 : getN CN 0 = 8748 := by rw [ds_eq.2]; rfl

theorem cn_pos : ∀ i < 34, 0 < getN CN i := by
  rw [ds_eq.2]
  decide

theorem cn_sum : ∑ i : Fin 34, 8748 / getN CN i = 729 := by
  rw [ds_eq.2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

theorem t6_mem : [6, 6] ∈ fiCoverCodes := by decide +kernel

theorem gWord_eq (c : ℕ) :
    gWord INVM RW c = if c % 2 = 1 then wInv INVM (RW (c / 2)) else RW (c / 2) := by
  unfold gWord
  have h1 : Nat.shiftRight c 1 = c / 2 := by
    rw [show Nat.shiftRight c 1 = c >>> 1 from rfl, Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_neg (by norm_num)]
    rfl
  · rw [h, if_pos rfl]
    rfl

theorem ivL_lt {c : ℕ} (hc : c < 12) : ivL INVM c < 12 := (hinv c hc).1

theorem evalWord_rev_inv {G : Type*} [Group G] {y : ℕ → G} :
    ∀ {l : List ℕ}, (∀ c ∈ l, y (ivL INVM c) = (y c)⁻¹) →
      evalWord y ((l.reverse).map (ivL INVM)) = (evalWord y l)⁻¹
  | [], _ => by simp [evalWord]
  | c :: l, h => by
    have ih := evalWord_rev_inv (y := y) (l := l) fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [evalWord, List.map_map] at ih ⊢
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [h c List.mem_cons_self]

theorem wInv_lt {r : ℕ} (hr : r < 44010) : ∀ d ∈ wList (wInv INVM (RW r)), d < 12 := by
  rw [(rec_ok r hr).2]
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
  exact ivL_lt ((rec_ok r hr).1 e (List.mem_reverse.1 he))

theorem gWord_lt {c : ℕ} (hc : c / 2 < 44010) : ∀ d ∈ wList (gWord INVM RW c), d < 12 := by
  rw [gWord_eq]
  split_ifs
  · exact wInv_lt hc
  · exact (rec_ok _ hc).1

theorem wVal_wInv {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {r : ℕ} (hr : r < 44010) : wVal y (wInv INVM (RW r)) = (wVal y (RW r))⁻¹ := by
  rw [wVal, (rec_ok r hr).2, evalWord_rev_inv fun c hc => hy c ((rec_ok r hr).1 c hc)]
  rfl

theorem wVal_gWord {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {c : ℕ} (hc : c / 2 < 44010) : wVal y (gWord INVM RW c) =
      if c % 2 = 1 then (wVal y (RW (c / 2)))⁻¹ else wVal y (RW (c / 2)) := by
  rw [gWord_eq]
  split_ifs
  · exact wVal_wInv hy hc
  · rfl

theorem isStabOf_sound {n k g : ℕ} (h : isStabOf RD n k g = true) :
    g < n ∧ 3 ≤ dKind (RD g) ∧ dKind (RD g) < 5 ∧ dN1 (RD g) = k ∧ dN2 (RD g) = k := by
  unfold isStabOf isEq at h
  simp only [kandB_iff, CFSG.Certificates.TwDce.Words.andB_iff, Nat.blt_eq, Nat.ble_eq,
    CFSG.Certificates.TwDce.Words.sB_eq] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem fb_eq : ∀ c < 12, ∀ p < 54, fieldAt 11 (FB c) p = fieldAt PB (F c) p :=
  CFSG.Certificates.TwDce3.repackOK_sound fb_ok.2.1

theorem fb_lt : ∀ c < 12, ∀ p < 54, fieldAt 11 (FB c) p < 54 :=
  fun c hc p hp => ((CFSG.Certificates.TwDce2.Rels.lettersOK_sound fb_ok.1 c hc).2 p hp).1

theorem f_lt : ∀ c < 12, ∀ p < 54, fieldAt PB (F c) p < 54 :=
  fun c hc p hp => fb_eq c hc p hp ▸ fb_lt c hc p hp

theorem f_id {c : ℕ} (hc : c < 12) (h6 : 6 ≤ c) {p : ℕ} (hp : p < 54) :
    fieldAt PB (F c) p = p := by
  have hm : [c] ∈ idCodes := by
    have : c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact (CFSG.Certificates.TwDce3.relsOK_sound fb_ok.2.2 (by decide) [c] hm).2 p hp

theorem fo_lt : ∀ c < 12, ∀ x < 8748, fieldAt 14 (FO c) x < 8748 :=
  fun c hc x hx => ((CFSG.Certificates.TwDce3.lettersOK_sound letters_ok c hc).2 x hx).1

theorem tu_facts : TU 0 = BS ∧ ∀ p < 8748, (∀ i < NB, CFSG.KC.TwDce.fld (TU p) (16 * i) 65535 < 54) ∧
    ∀ c < 12, ∀ i < NB, CFSG.KC.TwDce.fld (TU (fieldAt 14 (FO c) p)) (16 * i) 65535 =
      fieldAt PB (F c) (CFSG.KC.TwDce.fld (TU p) (16 * i) 65535) :=
  CFSG.Certificates.TwDce3.tupleOK_sound tuple_ok

theorem omega_walk : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < 8748,
    w.foldl (fun q c => fieldAt 14 (FO c) q) p < 8748 ∧ ∀ i < NB,
      CFSG.KC.TwDce.fld (TU (w.foldl (fun q c => fieldAt 14 (FO c) q) p)) (16 * i) 65535 =
        w.foldl (fun q c => fieldAt PB (F c) q) (CFSG.KC.TwDce.fld (TU p) (16 * i) 65535) :=
  CFSG.Certificates.TwDce3.tuple_foldl fo_lt (fun p hp => (tu_facts.2 p hp).2)

theorem evP_list (w x : ℕ) :
    CFSG.KC.TwDce3.evP 14 FO w x = (wList w).foldl (fun p c => fieldAt 14 (FO c) p) x :=
  CFSG.Certificates.TwDce3.Words.evP_eq 14 FO w x

theorem cover_all : ∀ i < 34, ∀ p < 8748,
    CFSG.Certificates.TwDce3.Reached 14 FO INVM RD RW 44010 DS (getN DS i) p := by
  intro i hi p hp
  have h0 := CFSG.Certificates.TwDce3.coverRange_sound cover0
  have h1 := CFSG.Certificates.TwDce3.coverRange_sound cover1
  have h2 := CFSG.Certificates.TwDce3.coverRange_sound cover2
  have h3 := CFSG.Certificates.TwDce3.coverRange_sound cover3
  have h4 := CFSG.Certificates.TwDce3.coverRange_sound cover4
  have h5 := CFSG.Certificates.TwDce3.coverRange_sound cover5
  by_cases i5 : i < 5
  · simpa using h0 i i5 p hp
  by_cases i10 : i < 10
  · simpa [show 5 + (i - 5) = i by omega] using h1 (i - 5) (by omega) p hp
  by_cases i15 : i < 15
  · simpa [show 10 + (i - 10) = i by omega] using h2 (i - 10) (by omega) p hp
  by_cases i21 : i < 21
  · simpa [show 15 + (i - 15) = i by omega] using h3 (i - 15) (by omega) p hp
  by_cases i27 : i < 27
  · simpa [show 21 + (i - 21) = i by omega] using h4 (i - 21) (by omega) p hp
  · simpa [show 27 + (i - 27) = i by omega] using h5 (i - 27) (by omega) p hp

theorem stab_i {i : ℕ} (hi : i < 34) : stabOK FB INVM 54 RD RW 44010 (getN DS i) (getL CG i)
    (getLL CW i) (getLL CB i) (getLL CS i) (getLL CT i) (getN CN i) = true := by
  simpa using CFSG.Certificates.TwDce3.stabRange_sound stab_ok i hi

theorem stabs_sound {k : ℕ} : ∀ {L : List ℕ}, (List.rec (motive := fun _ => Bool) true
    (fun c _ ih => CFSG.KC.andB (isStabOf RD 44010 k (Nat.shiftRight c 1)) ih) L) = true →
    ∀ c ∈ L, isStabOf RD 44010 k (c / 2) = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | d :: L, h, c, hc => by
    change CFSG.KC.andB (isStabOf RD 44010 k (Nat.shiftRight d 1)) _ = true at h
    rw [kandB_iff] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · have e : Nat.shiftRight c 1 = c / 2 := by
        rw [show Nat.shiftRight c 1 = c >>> 1 from rfl, Nat.shiftRight_eq_div_pow, pow_one]
      rw [← e]
      exact h.1
    · exact stabs_sound h.2 c hc

theorem cg_stab {i : ℕ} (hi : i < 34) : ∀ c ∈ getL CG i,
    isStabOf RD 44010 (getN DS i) (c / 2) = true :=
  stabs_sound (kandB_iff.1 (stab_i hi)).1

theorem fiT_sq : fiT * fiT = 1 := by
  have h := evalWord_codes t6_mem
  simpa [evalWord, CFSG.Certificates.TwDce2.wdVal, topCode] using h

theorem fiH_gen : Subgroup.closure ((fiH : Set fiPC) ∪ {fiT}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj : j.val < 3
  · refine Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ?_))
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  · have e : j = 3 := Fin.ext (by have := j.isLt; omega)
    rw [e]
    exact Subgroup.subset_closure (Or.inr rfl)

theorem wVal_mem (w : ℕ) : wVal fiX w ∈ fiH := by
  rw [wVal, evalWord]
  refine fiH.list_prod_mem fun y hy => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
  by_cases hc : c < 12
  · exact hxH c hc
  · rw [fiX, if_neg (by omega)]
    exact fiH.one_mem

theorem relIndex_map_le {Q : Type*} [Group Q] [Finite Q] (π : Q →* fiPC) (P : Subgroup Q) :
    (P.map π).relIndex π.range ≤ P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

structure HAct (Q : Type*) [Group Q] where
  π : Q →* fiPC
  xq : ℕ → Q
  π_xq : ∀ c < 12, π (xq c) = fiX c
  xq_inv : ∀ c < 12, xq (ivL INVM c) = (xq c)⁻¹
  gen : ∀ q : Q, ∃ w : List ℕ, (∀ c ∈ w, c < 12) ∧ q = evalWord xq w
  pt : Q → ℕ → ℕ
  pt_one : ∀ p, pt 1 p = p
  pt_mul : ∀ a b p, pt (a * b) p = pt b (pt a p)
  pt_xq : ∀ c < 12, ∀ p < 54, pt (xq c) p = fieldAt PB (F c) p

namespace HAct

variable {Q : Type*} [Group Q] (A : HAct Q)
include A

theorem pt_eval : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < 54,
    A.pt (evalWord A.xq w) p = w.foldl (fun p c => fieldAt PB (F c) p) p
  | [], _, p, _ => A.pt_one p
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    rw [evalWord_cons, A.pt_mul, A.pt_xq c hc p hp, List.foldl_cons]
    exact pt_eval w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) _ (f_lt c hc p hp)

theorem foldl_lt : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < 54,
    w.foldl (fun p c => fieldAt PB (F c) p) p < 54
  | [], _, _, hp => hp
  | c :: w, hw, p, hp => foldl_lt w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) _
      (f_lt c (hw c List.mem_cons_self) p hp)

theorem pt_lt (q : Q) {p : ℕ} (hp : p < 54) : A.pt q p < 54 := by
  obtain ⟨w, hw, rfl⟩ := A.gen q
  rw [A.pt_eval w hw p hp]
  exact A.foldl_lt w hw p hp

theorem hxFB : ∀ c < 12, ∀ p < 54, fieldAt 11 (FB c) p = A.pt (A.xq c) p := fun c hc p hp => by
  rw [fb_eq c hc p hp, A.pt_xq c hc p hp]

theorem evalWord_pi : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → A.π (evalWord A.xq w) = evalWord fiX w
  | [], _ => by simp [evalWord]
  | c :: w, hw => by
    rw [evalWord_cons, evalWord_cons, map_mul, A.π_xq c (hw c List.mem_cons_self),
      evalWord_pi w fun d hd => hw d (List.mem_cons_of_mem _ hd)]

theorem range_pi : A.π.range = fiH := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    obtain ⟨w, hw, rfl⟩ := A.gen q
    rw [A.evalWord_pi w hw, evalWord]
    refine fiH.list_prod_mem fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hxH c (hw c hc)
  · refine (Subgroup.closure_le _).2 ?_
    have h0 : (PresentedGroup.of 0 : fiPC) = A.π (A.xq 2) := by rw [A.π_xq 2 (by norm_num)]; rfl
    have h1 : (PresentedGroup.of 1 : fiPC) = A.π (A.xq 0) := by rw [A.π_xq 0 (by norm_num)]; rfl
    have h2 : (PresentedGroup.of 2 : fiPC) = A.π (A.xq 4) := by rw [A.π_xq 4 (by norm_num)]; rfl
    intro g hg
    rcases hg with rfl | rfl | hg
    · exact ⟨_, h0.symm⟩
    · exact ⟨_, h1.symm⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact ⟨_, h2.symm⟩

noncomputable def St (i : ℕ) : Subgroup Q :=
  Subgroup.closure {q | ∃ c, isStabOf RD 44010 (getN DS i) (c / 2) = true ∧
    q = wVal A.xq (gWord INVM RW c)}

noncomputable def Kg (i : ℕ) : Subgroup Q :=
  Subgroup.closure {q | ∃ c ∈ getL CG i, q = wVal A.xq (gWord INVM RW c)}

theorem Kg_le_St {i : ℕ} (hi : i < 34) : A.Kg i ≤ A.St i := by
  rw [Kg, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.subset_closure ⟨c, cg_stab hi c hc, rfl⟩

variable [Finite Q]

theorem card_Kg_ge {i : ℕ} (hi : i < 34) : getN CN i ≤ Nat.card (A.Kg i) := by
  have hs := chainB_sound (G := Q) A.xq A.pt A.pt_one A.pt_mul fb_lt A.hxFB (A.Kg i)
    (fun c hc => ⟨gens_ok i hi c hc, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩) (lens_ok i hi)
    (kandB_iff.1 (stab_i hi)).2
  have : Nonempty {g : Q // g ∈ A.Kg i ∧ ∀ b ∈ getLL CB i,
      A.pt g (colDat 11 b / 2) = colDat 11 b / 2} :=
    ⟨⟨1, Subgroup.one_mem _, fun b _ => A.pt_one _⟩⟩
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) hs

variable (hQ : Nat.card Q ≤ 8748)
include hQ

theorem pt_eq_one {q : Q} (hq : ∀ i < NB, A.pt q (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
    CFSG.KC.TwDce.fld BS (16 * i) 65535) : q = 1 := by
  have hch : chainB FB 54 (getLL CW 0) (getLL CB 0) (getLL CS 0) (getLL CT 0)
      (gRegs INVM RW (getL CG 0)) 8748 = true := by
    have h := (kandB_iff.1 (stab_i (i := 0) (by norm_num))).2
    rwa [cn0] at h
  have hs := chainB_sound (G := Q) A.xq A.pt A.pt_one A.pt_mul fb_lt A.hxFB ⊤
    (fun c hc => ⟨gens_ok 0 (by norm_num) c hc, Subgroup.mem_top _⟩) (lens_ok 0 (by norm_num)) hch
  rw [Subgroup.card_top] at hs
  have : Finite {g : Q // g ∈ (⊤ : Subgroup Q) ∧ ∀ b ∈ getLL CB 0,
      A.pt g (colDat 11 b / 2) = colDat 11 b / 2} := Subtype.finite
  have hne : Nonempty {g : Q // g ∈ (⊤ : Subgroup Q) ∧ ∀ b ∈ getLL CB 0,
      A.pt g (colDat 11 b / 2) = colDat 11 b / 2} :=
    ⟨⟨1, Subgroup.mem_top _, fun b _ => A.pt_one _⟩⟩
  have h1 : Nat.card {g : Q // g ∈ (⊤ : Subgroup Q) ∧ ∀ b ∈ getLL CB 0,
      A.pt g (colDat 11 b / 2) = colDat 11 b / 2} ≤ 1 := by
    by_contra h
    have h2 : 8748 * 2 ≤ 8748 * Nat.card {g : Q // g ∈ (⊤ : Subgroup Q) ∧ ∀ b ∈ getLL CB 0,
        A.pt g (colDat 11 b / 2) = colDat 11 b / 2} := Nat.mul_le_mul_left _ (by omega)
    omega
  have hsub := Finite.card_le_one_iff_subsingleton.1 h1
  have hmem : ∀ g : Q, (∀ i < NB, A.pt g (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → g ∈ (⊤ : Subgroup Q) ∧ ∀ b ∈ getLL CB 0,
        A.pt g (colDat 11 b / 2) = colDat 11 b / 2 := by
    intro g hg
    refine ⟨Subgroup.mem_top _, fun b hb => ?_⟩
    obtain ⟨i, hi, he⟩ := base_ok.2 b hb
    rw [he]
    exact hg i hi
  exact congrArg Subtype.val (hsub.elim ⟨q, hmem q hq⟩ ⟨1, hmem 1 fun i _ => A.pt_one _⟩)

theorem hone_fi : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
    (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord fiX w = 1 := by
  intro w hw hfix
  rw [← A.evalWord_pi w hw, A.pt_eq_one hQ (q := evalWord A.xq w)
    (fun i hi => by rw [A.pt_eval w hw _ (base_ok.1 i hi)]; exact hfix i hi), map_one]

omit hQ in
theorem idx_St_le (hQ : Nat.card Q ≤ 8748) {i : ℕ} (hi : i < 34) :
    (A.St i).index ≤ 8748 / getN CN i := by
  rw [Nat.le_div_iff_mul_le (cn_pos i hi)]
  have h1 := (A.card_Kg_ge hi).trans (Subgroup.card_le_of_le (A.Kg_le_St hi))
  calc (A.St i).index * getN CN i ≤ (A.St i).index * Nat.card (A.St i) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.card Q := (A.St i).index_mul_card
    _ ≤ 8748 := hQ

omit hQ in
theorem exists_tuple (q : Q) : ∃ p < 8748, ∀ i < NB,
    CFSG.KC.TwDce.fld (TU p) (16 * i) 65535 = A.pt q (CFSG.KC.TwDce.fld BS (16 * i) 65535) := by
  obtain ⟨w, hw, rfl⟩ := A.gen q
  obtain ⟨h1, h2⟩ := omega_walk w hw 0 (by norm_num)
  refine ⟨_, h1, fun i hi => ?_⟩
  rw [h2 i hi, tu_facts.1, A.pt_eval w hw _ (base_ok.1 i hi)]

omit hQ in
theorem walk_tuple {w : List ℕ} (hw : ∀ c ∈ w, c < 12) {p : ℕ} (hp : p < 8748) {y : Q}
    (hy : ∀ i < NB, CFSG.KC.TwDce.fld (TU p) (16 * i) 65535 =
      A.pt y (CFSG.KC.TwDce.fld BS (16 * i) 65535)) :
    w.foldl (fun q c => fieldAt 14 (FO c) q) p < 8748 ∧ ∀ i < NB,
      CFSG.KC.TwDce.fld (TU (w.foldl (fun q c => fieldAt 14 (FO c) q) p)) (16 * i) 65535 =
        A.pt (y * evalWord A.xq w) (CFSG.KC.TwDce.fld BS (16 * i) 65535) := by
  obtain ⟨h1, h2⟩ := omega_walk w hw p hp
  refine ⟨h1, fun i hi => ?_⟩
  rw [h2 i hi, hy i hi, A.pt_mul, A.pt_eval w hw _ (A.pt_lt y (base_ok.1 i hi))]

omit hQ in
theorem fold_tuple : ∀ (cs : List ℕ), (∀ c ∈ cs, c / 2 < 44010) → ∀ (p : ℕ) (y : Q), p < 8748 →
    (∀ i < NB, CFSG.KC.TwDce.fld (TU p) (16 * i) 65535 =
      A.pt y (CFSG.KC.TwDce.fld BS (16 * i) 65535)) →
    cs.foldl (fun q c => CFSG.KC.TwDce3.evP 14 FO (gWord INVM RW c) q) p < 8748 ∧ ∀ i < NB,
      CFSG.KC.TwDce.fld
        (TU (cs.foldl (fun q c => CFSG.KC.TwDce3.evP 14 FO (gWord INVM RW c) q) p)) (16 * i) 65535 =
      A.pt (y * (cs.map fun c => wVal A.xq (gWord INVM RW c)).prod)
        (CFSG.KC.TwDce.fld BS (16 * i) 65535)
  | [], _, p, y, hp, hy => ⟨hp, fun i hi => by
      rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
      exact hy i hi⟩
  | c :: cs, hcs, p, y, hp, hy => by
    have hc := hcs c List.mem_cons_self
    obtain ⟨h1, h2⟩ := A.walk_tuple (gWord_lt hc) hp hy
    rw [← evP_list] at h1 h2
    obtain ⟨h3, h4⟩ := fold_tuple cs (fun d hd => hcs d (List.mem_cons_of_mem _ hd)) _ _ h1 h2
    refine ⟨h3, fun i hi => ?_⟩
    rw [List.foldl_cons, h4 i hi, List.map_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem rep_cover_Q {i : ℕ} (hi : i < 34) (q : Q) : ∃ f < 44010, dKind (RD f) < 3 ∧
    dN1 (RD f) = getN DS i ∧ dN2 (RD f) ∈ DS ∧ ∃ g ∈ A.St i, q = g⁻¹ * wVal A.xq (RW f) := by
  obtain ⟨p, hp, hpq⟩ := A.exists_tuple q⁻¹
  obtain ⟨f, hf, hfa, hk, hnd, cs, hcs, hpe⟩ := cover_all i hi p hp
  have hcs' : ∀ c ∈ cs, c / 2 < 44010 := fun c hc => (isStabOf_sound (hcs c hc)).1
  have h0 : ∀ i < NB, CFSG.KC.TwDce.fld (TU 0) (16 * i) 65535 =
      A.pt 1 (CFSG.KC.TwDce.fld BS (16 * i) 65535) := fun i _ => by rw [A.pt_one, tu_facts.1]
  obtain ⟨h1, h2⟩ := A.walk_tuple (wInv_lt hf) (by norm_num) h0
  rw [← evP_list] at h1 h2
  simp only [one_mul] at h2
  obtain ⟨-, h4⟩ := A.fold_tuple cs hcs' _ _ h1 h2
  rw [← hpe] at h4
  set g := (cs.map fun c => wVal A.xq (gWord INVM RW c)).prod with hg
  have hgS : g ∈ A.St i := by
    refine (A.St i).list_prod_mem fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact Subgroup.subset_closure ⟨c, hcs c hc, rfl⟩
  have hwi : evalWord A.xq (wList (wInv INVM (RW f))) = (wVal A.xq (RW f))⁻¹ :=
    wVal_wInv A.xq_inv hf
  rw [hwi] at h4
  have hfix : ∀ j < NB, A.pt ((wVal A.xq (RW f))⁻¹ * g * q) (CFSG.KC.TwDce.fld BS (16 * j) 65535) =
      CFSG.KC.TwDce.fld BS (16 * j) 65535 := by
    intro j hj
    rw [A.pt_mul, ← h4 j hj, hpq j hj, ← A.pt_mul, inv_mul_cancel, A.pt_one]
  have he := A.pt_eq_one hQ hfix
  refine ⟨f, hf, Nat.blt_eq.mp hfa, hk, hnd, g, hgS, ?_⟩
  rw [mul_assoc] at he
  have := eq_inv_of_mul_eq_one_right he
  rw [inv_inv] at this
  rw [eq_inv_mul_iff_mul_eq]
  exact this

theorem index_fiH_le : fiH.FiniteIndex ∧ fiH.index ≤ 729 := by
  classical
  obtain ⟨X, hX0, hX⟩ := facts (A.hone_fi hQ)
  have hrange := A.range_pi
  have hy : ∀ c < 12, fiX (ivL INVM c) = (fiX c)⁻¹ := fun c hc => (hinv c hc).2
  let repS : Fin 34 → Set fiPC := fun i => {k | ∃ f < 44010, dKind (RD f) < 3 ∧
    dN1 (RD f) = getN DS i ∧ dN2 (RD f) ∈ DS ∧ k = wVal fiX (RW f)}
  let tP : Fin 34 → fiPC → Prop := fun i k =>
    ∃ j : Fin 34, ∃ v, v ∈ fiH ∧ X (getN DS i) * k * fiT * (X (getN DS j) * v)⁻¹ ∈ fiH
  have htP : ∀ i : Fin 34, ∀ k ∈ repS i, tP i k := by
    rintro i _ ⟨f, hf, hk, hn1, hn2, rfl⟩
    obtain ⟨j, hj, hje⟩ := ds_mem _ hn2
    refine ⟨⟨j, hj⟩, wVal fiX (RA f), wVal_mem _, ?_⟩
    have hfa := (hX f hf).2.2.2.1 hk
    rw [hn1, ← hje] at hfa
    exact hfa
  let D : CFSG.Certificates.TwDce.TwistData fiH ⊥ fiT 34 :=
    { x := fun i => X (getN DS i)
      S := fun i => (A.St i).map A.π
      rep := repS
      tgt := fun i k => if h : tP i k then h.choose else 0
      tgtElt := fun i k => if h : tP i k then h.choose_spec.choose else 1
      base := 0
      base_mem := by
        change X (getN DS 0) ∈ fiH
        rw [ds0, hX0]
        exact fiH.one_mem
      S_le := fun i => by
        rw [← hrange]
        exact Subgroup.map_le_range _ _
      S_conj := by
        rintro i _ ⟨q, hq, rfl⟩
        induction hq using Subgroup.closure_induction with
        | mem q hq =>
          obtain ⟨c, hc, rfl⟩ := hq
          obtain ⟨hg, hk3, -, hn1, hn2⟩ := isStabOf_sound hc
          have hf := (hX (c / 2) hg).2.2.2.2 hk3
          rw [hn1, hn2] at hf
          rw [wVal, A.evalWord_pi _ (gWord_lt hg), ← wVal, wVal_gWord hy hg]
          split_ifs
          · convert hf using 1
            group
          · convert fiH.inv_mem hf using 1
            group
        | one => rw [map_one, mul_one, mul_inv_cancel]; exact fiH.one_mem
        | mul a b _ _ ha hb =>
          have e : X (getN DS i) * A.π (a * b) * (X (getN DS i))⁻¹ =
              (X (getN DS i) * A.π a * (X (getN DS i))⁻¹) *
                (X (getN DS i) * A.π b * (X (getN DS i))⁻¹) := by
            rw [map_mul]; group
          rw [e]
          exact fiH.mul_mem ha hb
        | inv a _ ha =>
          have e : X (getN DS i) * A.π a⁻¹ * (X (getN DS i))⁻¹ =
              (X (getN DS i) * A.π a * (X (getN DS i))⁻¹)⁻¹ := by
            rw [map_inv]; group
          rw [e]
          exact fiH.inv_mem ha
      rep_le := by
        rintro i _ ⟨f, -, -, -, -, rfl⟩
        exact wVal_mem _
      rep_cover := by
        intro i h hh
        rw [← hrange] at hh
        obtain ⟨q, rfl⟩ := hh
        obtain ⟨f, hf, hk, hn1, hn2, g, hg, hq⟩ := A.rep_cover_Q hQ i.2 q
        refine ⟨wVal fiX (RW f), ⟨f, hf, hk, hn1, hn2, rfl⟩, A.π g⁻¹,
          ⟨g⁻¹, (A.St i).inv_mem hg, rfl⟩, 1, Subgroup.one_mem _, ?_⟩
        rw [hq, map_mul, mul_one, wVal, A.evalWord_pi _ (rec_ok f hf).1]
        rfl
      tgtElt_mem := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.1
      tgt_spec := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.2 }
  have : Finite fiH := by
    rw [← hrange]
    exact Finite.of_surjective _ A.π.rangeRestrict_surjective
  obtain ⟨hfi, hle⟩ := D.index_le_sum fiT_sq (fun c hc => by
      rw [Subgroup.mem_bot.1 hc, mul_one, inv_mul_cancel]
      exact fiH.one_mem) fiH_gen
  refine ⟨hfi, hle.trans ?_⟩
  calc ∑ i, (D.S i).relIndex fiH ≤ ∑ i : Fin 34, 8748 / getN CN i :=
        Finset.sum_le_sum fun i _ => by
          change ((A.St i).map A.π).relIndex fiH ≤ _
          rw [← hrange]
          exact (relIndex_map_le A.π (A.St i)).trans (A.idx_St_le hQ i.2)
    _ = 729 := cn_sum

theorem card_fiPC_le : Finite fiPC ∧ Nat.card fiPC ≤ 6377292 := by
  obtain ⟨hfi, hidx⟩ := A.index_fiH_le hQ
  have hrange := A.range_pi
  have : Finite fiH := by
    rw [← hrange]
    exact Finite.of_surjective _ A.π.rangeRestrict_surjective
  have hH : Nat.card fiH ≤ 8748 := by
    rw [← hrange]
    exact (Nat.card_le_card_of_surjective _ A.π.rangeRestrict_surjective).trans hQ
  have : Finite (fiPC ⧸ fiH) := Subgroup.finite_quotient_of_finiteIndex
  have hf : Finite fiPC := Finite.of_subgroup_quotient fiH
  refine ⟨hf, ?_⟩
  rw [← fiH.index_mul_card]
  calc fiH.index * Nat.card fiH ≤ 729 * 8748 := Nat.mul_le_mul hidx hH
    _ = 6377292 := by norm_num

end HAct

end CFSG.KD.Fi23Dce3

end
