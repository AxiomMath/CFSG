module

public import Certificates.Kernel.TwoHS.HarCGlue
public import Certificates.Kernel.TwoHS.HarSylK
public import CFSG.Certificates.Kernel.PosWalkSound
public import CFSG.Certificates.Kernel.BfsPairsSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PosWalk
open CFSG.KC.Loop CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

@[expose] noncomputable def syET (x : Nat) : Table := tabT (unpack 11200 14 (TE.T x))

@[expose] noncomputable def syE (x : Nat) : Equiv.Perm (Fin 11200) := tablePerm 11200 (syET x)

@[expose] noncomputable def syG (l : Nat) : Equiv.Perm (Fin 11200) :=
  if l < 3 then tp 11200 (harU.getD l (idT 11200)) else (tp 11200 (harU.getD (l - 3) (idT 11200)))⁻¹

@[expose] noncomputable def syH (l : Nat) : Equiv.Perm (Fin 11200) := ((syGet l).map syG).prod

theorem sy_hn : (11200 : Nat) < 2 ^ 32 := by norm_num

theorem sy_cnt : TE.cnt = 1024 := base_parts.2.1

theorem sy_hh : penumHdK idK TE.cnt 2000 TE.T TE.PL = true := base_parts.2.2.1

theorem sy_canon : ∀ q < TE.cnt, Cn (TE.T q) := fun q hq => penumPt_canon (sE q hq)

theorem sy_perm_harU : ∀ g ∈ harU, permOK 11200 g = true := by
  intro g hg
  have h := List.all_eq_true.1 (perm_all TE_tabs TE_inv) g hg
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem sy_enum : enumOK 11200 2000 1024 harU = true :=
  CFSG.KS.MulH.enumOK_of hn TE_G TE_tabs TE_inv sy_hh sE sH sCl sy_cnt

theorem sy_closure : mulClosureH 11200 harU.toArray 2000 = hRec 11200 14 TE.cnt TE.T TE.PL :=
  (mulH_sound hn TE_G TE_tabs sy_hh sE sH).1

theorem sy_size : (mulClosureH 11200 harU.toArray 2000).1.size = 1024 := by
  rw [sy_closure, hRec_size, sy_cnt]

theorem sy_get {x : Nat} (hx : x < 1024) : (mulClosureH 11200 harU.toArray 2000).1[x]! = syET x := by
  rw [sy_closure]
  exact hRec_get (by rw [sy_cnt]; exact hx)

theorem syE_rep {x : Nat} (hx : x < 1024) : Rep 11200 (syET x) (syE x) ∧ syE x ∈ genOf 11200 harU := by
  obtain ⟨-, hrep, -, -⟩ := CFSG.Sporadic.SmallOddCore.enumOK_spec sy_hn sy_perm_harU sy_enum
  have h := hrep x (by rw [sy_size]; exact hx)
  rw [sy_get hx] at h
  exact h

theorem syE_mem {x : Nat} (hx : x < 1024) : syE x ∈ genOf 11200 harU := (syE_rep hx).2

theorem syE_cover {y : Equiv.Perm (Fin 11200)} (hy : y ∈ genOf 11200 harU) :
    ∃ x < 1024, syE x = y := by
  obtain ⟨-, -, hcov, -⟩ := CFSG.Sporadic.SmallOddCore.enumOK_spec sy_hn sy_perm_harU sy_enum
  obtain ⟨k, hk, hr⟩ := hcov y hy
  rw [sy_size] at hk
  rw [sy_get hk] at hr
  exact ⟨k, hk, rep_unique (syE_rep hk).1 hr⟩

theorem sy_T_inj : ∀ a < TE.cnt, ∀ b < TE.cnt, TE.T a = TE.T b → a = b :=
  inj_of_sortH (S := r32 TE.SRT) (SI := r32 TE.SRI) fun i hi => (penumPt_specH (sE i hi)).2.2.2

theorem syE_inj {x y : Nat} (hx : x < 1024) (hy : y < 1024) (h : syE x = syE y) : x = y := by
  have h1 := (tblEq_iff_eq (syE_rep hx).1 (syE_rep hy).1).2 h
  have hx' : x < TE.cnt := by rw [sy_cnt]; exact hx
  have hy' : y < TE.cnt := by rw [sy_cnt]; exact hy
  unfold syET at h1
  rw [CFSG.KD.TwoHS.tblEq_eq (sy_canon x hx') (sy_canon y hy')] at h1
  exact sy_T_inj x hx' y hy' (Nat.eq_of_beq_eq_true h1)

theorem syE_eq_iff {x y : Nat} (hx : x < 1024) (hy : y < 1024) : syE x = syE y ↔ x = y :=
  ⟨syE_inj hx hy, fun h => by rw [h]⟩

theorem syE_zero : syE 0 = 1 := by
  have h := sy_hh
  unfold penumHdK at h
  simp only [bAnd_iff] at h
  have e : TE.T 0 = idK := Nat.eq_of_beq_eq_true h.2.2.1
  have hr : Rep 11200 (syET 0) (1 : Equiv.Perm (Fin 11200)) := by
    unfold syET
    rw [e, ← idT_eq]
    exact Rep.idT sy_hn
  exact rep_unique (syE_rep (by norm_num)).1 hr

theorem sy_T0_set : (genOf 11200 harU : Set (Equiv.Perm (Fin 11200))) = syE '' {x | x < 1024} := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := syE_cover hy
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact syE_mem hx

theorem syU_len : harU.length = 3 := rfl

theorem syU_getD {j : Nat} (hj : j < 3) :
    harU.getD j (idT 11200) = tabT (unpack 11200 14 (TE.GI j)) ∧ Cn (TE.GI j) := by
  obtain ⟨h1, h2⟩ := TE_tabs.2 j hj
  rw [getElem!_pos _ j (by rw [List.size_toArray, syU_len]; exact hj), List.getElem_toArray] at h1
  rw [List.getD_eq_getElem _ _ (by rw [syU_len]; exact hj)]
  exact ⟨h1, h2⟩

theorem syU_getD_mem {j : Nat} (hj : j < 3) : harU.getD j (idT 11200) ∈ harU := by
  rw [List.getD_eq_getElem _ _ (by rw [syU_len]; exact hj)]
  exact List.getElem_mem _

theorem syG_eq_tp {j : Nat} (hj : j < harU.length) : syG j = tp 11200 harU[j] := by
  have h3 : j < 3 := by rwa [syU_len] at hj
  have e : harU.getD j (idT 11200) = harU[j] := List.getD_eq_getElem _ _ hj
  simp only [syG, if_pos h3, e]
  rfl

theorem syG_rep {l : Nat} (hl : l < 6) :
    Rep 11200 (tabT (unpack 11200 14 (bothK 3 TE.GI TEI l))) (syG l) := by
  by_cases h3 : l < 3
  · rw [bothK_lt h3, ← (syU_getD h3).1]
    unfold syG
    rw [if_pos h3]
    exact rep_tp (sy_perm_harU _ (syU_getD_mem h3))
  · have hj : l - 3 < 3 := by omega
    rw [bothK_ge (by omega), ← invT_eq (TE_inv _ hj).1, ← (syU_getD hj).1]
    unfold syG
    rw [if_neg h3]
    exact rep_invT_of_rep sy_hn (rep_tp (sy_perm_harU _ (syU_getD_mem hj)))

theorem sy_hcl : ∀ x < 1024, ∀ l < 6,
    wstepK TECl 6 x l < 1024 ∧ syE (wstepK TECl 6 x l) = syE x * syG l := by
  intro x hx l hl
  have hc : x * 6 + l < TE.cnt * (3 + 3) := by rw [sy_cnt]; omega
  obtain ⟨h1, h2⟩ := findPt_spec (sCl _ hc)
  have e : wstepK TECl 6 x l = r32 TECl (x * 6 + l) := by
    unfold wstepK
    congr 1
    change 6 * x + l = x * 6 + l
    omega
  obtain ⟨e1, e2⟩ := div_mod_pair (i := x) (K := 6) hl
  unfold prodQK at h2
  rw [show Nat.div (x * 6 + l) 6 = x from e1, show Nat.mod (x * 6 + l) 6 = l from e2] at h2
  rw [e]
  rw [sy_cnt] at h1
  refine ⟨h1, ?_⟩
  have hx' : x < TE.cnt := by rw [sy_cnt]; exact hx
  have hcan : Cn (bothK 3 TE.GI TEI l) := by
    by_cases h3 : l < 3
    · rw [bothK_lt h3]
      exact (syU_getD h3).2
    · rw [bothK_ge (by omega)]
      exact (TE_inv _ (by omega)).2
  have hr : Rep 11200 (syET (r32 TECl (x * 6 + l))) (syE x * syG l) := by
    have hc := Rep.compT (syE_rep hx).1 (syG_rep hl)
    unfold syET at hc
    rw [CFSG.KD.TwoHS.comp_eq (sy_canon x hx') hcan] at hc
    unfold syET
    rw [h2]
    exact hc
  exact rep_unique (syE_rep h1).1 hr

theorem foldl_mul_eq {M : Type*} [Monoid M] (g : Nat → M) :
    ∀ (wd : List Nat) (a : M), wd.foldl (fun a l => a * g l) a = a * (wd.map g).prod
  | [], a => by simp
  | l :: wd, a => by
    rw [List.foldl_cons, foldl_mul_eq g wd, List.map_cons, List.prod_cons, mul_assoc]

theorem sy_walk {wd : List Nat} (hw : ∀ l ∈ wd, l < 6) {x : Nat} (hx : x < 1024) :
    walkK TECl 6 wd x < 1024 ∧ syE (walkK TECl 6 wd x) = syE x * (wd.map syG).prod := by
  obtain ⟨h1, h2⟩ := walk_sound (T := syE) (G := syG) (pc := fun a b => a * b) sy_hcl wd hw x hx
  exact ⟨h1, h2.trans (foldl_mul_eq syG wd (syE x))⟩

theorem sy_tree : ∀ y < 1024, y ≠ 0 → parOf TE.PL y < y ∧ labOf TE.PL y < 6 ∧
    syE y = syE (parOf TE.PL y) * syG (labOf TE.PL y) := by
  intro y hy hy0
  have hy' : y < TE.cnt := by rw [sy_cnt]; exact hy
  obtain ⟨hp, hl, ht, -⟩ := (penumPt_specH (sE y hy')).2.1 hy0
  refine ⟨hp, by omega, ?_⟩
  have hpc : parOf TE.PL y < TE.cnt := by omega
  have e : TE.T y = pc (pc idK (TE.T (parOf TE.PL y))) (TE.GI (labOf TE.PL y)) := by
    rw [ht]
    unfold stepK
    rw [TE_G _ hl]
    rfl
  have hr : Rep 11200 (syET y) (1 * syE (parOf TE.PL y) * syG (labOf TE.PL y)) := by
    unfold syET
    rw [e, ← CFSG.KD.TwoHS.comp_eq (cPc cId (sy_canon _ hpc)) (syU_getD hl).2,
      ← CFSG.KD.TwoHS.comp_eq cId (sy_canon _ hpc), ← idT_eq]
    have hg := syG_rep (l := labOf TE.PL y) (by omega)
    rw [bothK_lt hl] at hg
    exact Rep.compT (Rep.compT (Rep.idT sy_hn) (syE_rep (by omega)).1) hg
  rw [one_mul] at hr
  exact rep_unique (syE_rep hy).1 hr

theorem syMul_eq {x y : Nat} (hx : x < 1024) (hy : y < 1024) :
    syMul x y < 1024 ∧ syE (syMul x y) = syE x * syE y :=
  pathPos_sound (T := syE) (G := syG) (pc := fun a b => a * b) sy_hcl sy_tree
    (fun _ _ _ _ _ _ => mul_assoc _ _ _)
    (fun x _ => by rw [syE_zero, mul_one]) 1024 y (le_of_lt hy) hy x hx

theorem syGet_eq (j : Nat) : syGet j = syGW.getD j [] := by
  unfold syGet
  generalize syGW = L
  induction L generalizing j with
  | nil => simp
  | cons a L ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ]
      exact ih j

theorem syGW_letters : ∀ w ∈ syGW, ∀ a ∈ w, a < 6 := by decide

theorem syGet_letters (j : Nat) : ∀ a ∈ syGet j, a < 6 := by
  rw [syGet_eq, List.getD_eq_getElem?_getD]
  cases h : syGW[j]? with
  | none => simp
  | some w => exact syGW_letters w (List.mem_of_getElem? h)

theorem syWalk_eq (l : Nat) {q : Nat} (hq : q < 1024) :
    syWalk l q < 1024 ∧ syE (syWalk l q) = syE q * syH l :=
  sy_walk (syGet_letters l) hq

@[expose] def syCW (p : List Nat × List Nat) : List Nat :=
  p.1.map (· - 1) ++ p.2.map (· - 1) ++ (p.1.reverse.map (· + 2) ++ p.2.reverse.map (· + 2))

theorem syGW_eq : syGW = harCPairs.map syCW ++ [[0], [1, 2, 2]] := by decide

@[expose] noncomputable def syU (w : List Nat) : Equiv.Perm (Fin 11200) := ((w.map (· - 1)).map syG).prod

theorem syU_rep {w : List Nat} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) : Rep 11200 (tU w) (syU w) := by
  have h := rep_wordTbl' sy_hn sy_perm_harU w (by rw [syU_len]; exact hw)
  have e : syU w = (w.map fun l => tp 11200 (harU.getD (l - 1) (idT 11200))).prod := by
    unfold syU
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro l hl
    have h3 : l - 1 < 3 := by have := hw l hl; omega
    simp only [Function.comp, syG, if_pos h3]
  rw [e]
  exact h

theorem syInv_mul : ∀ w : List Nat, (∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) →
    ((w.reverse.map (· + 2)).map syG).prod * ((w.map (· - 1)).map syG).prod = 1
  | [], _ => by simp
  | a :: w, hw => by
    have ha := hw a List.mem_cons_self
    have e : syG (a + 2) * syG (a - 1) = 1 := by
      have h3 : ¬ a + 2 < 3 := by omega
      have h4 : a - 1 < 3 := by omega
      have e' : a + 2 - 3 = a - 1 := by omega
      simp only [syG, if_neg h3, if_pos h4, e', inv_mul_cancel]
    have ih := syInv_mul w fun l hl => hw l (List.mem_cons_of_mem a hl)
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (syG (a + 2)), e, one_mul]
    exact ih

theorem syInv_word {w : List Nat} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    ((w.reverse.map (· + 2)).map syG).prod = (syU w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (syInv_mul w hw)

theorem syCW_prod {p : List Nat × List Nat} (h1 : ∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3)
    (h2 : ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ 3) : ((syCW p).map syG).prod = ⁅syU p.1, syU p.2⁆ := by
  unfold syCW
  rw [List.map_append, List.map_append, List.map_append, List.prod_append, List.prod_append,
    List.prod_append, syInv_word h1, syInv_word h2, commutatorElement_def]
  unfold syU
  simp only [mul_assoc]

theorem syPairs_letters : ∀ p ∈ harCPairs, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3) ∧ ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ 3 := by
  decide

theorem syC_len : harCgens.length = 5 := rfl

theorem syW_len : harWgens.length = 7 := rfl

theorem syPairs_len : harCPairs.length = 5 := rfl

theorem rep_map_get {l : List (List Nat × List Nat)} {F : List Nat × List Nat → Table} {j : Nat}
    (hj : j < (l.map F).length) {g : Equiv.Perm (Fin 11200)}
    (hr : Rep 11200 (F (l[j]'(by rw [List.length_map] at hj; exact hj))) g) :
    Rep 11200 (l.map F)[j] g := by
  rw [List.getElem_map]
  exact hr

theorem syC_rep : ∀ j (hj : j < harCgens.length), Rep 11200 harCgens[j] (syH j) := by
  intro j hj
  have h5 : j < 5 := by rwa [syC_len] at hj
  have hlp : j < harCPairs.length := by rw [syPairs_len]; exact h5
  have hl : j < (harCPairs.map syCW).length := by rw [List.length_map]; exact hlp
  have ew : syGet j = syCW (harCPairs[j]'hlp) := by
    rw [syGet_eq, syGW_eq, List.getD_eq_getElem _ _ (by
      rw [List.length_append, List.length_map, syPairs_len]; simp; omega),
      List.getElem_append_left hl, List.getElem_map]
  refine rep_map_get (l := harCPairs) (F := fun p => tComm 11200 (tU p.1) (tU p.2))
    (by rw [List.length_map]; exact hlp) ?_
  unfold syH
  have hp := syPairs_letters _ (List.getElem_mem hlp)
  rw [ew, syCW_prod hp.1 hp.2]
  exact rep_tComm sy_hn (syU_rep hp.1) (syU_rep hp.2)

theorem rep_append_left {l₁ l₂ : List Table} {j : Nat} {g : Equiv.Perm (Fin 11200)}
    (h : j < l₁.length) (hj : j < (l₁ ++ l₂).length) (hr : Rep 11200 l₁[j] g) :
    Rep 11200 (l₁ ++ l₂)[j] g := by
  rw [List.getElem_append_left h]
  exact hr

theorem rep_append_right {l₁ l₂ : List Table} {j : Nat} {g : Equiv.Perm (Fin 11200)}
    (h : l₁.length ≤ j) (hj : j < (l₁ ++ l₂).length)
    (hr : Rep 11200 (l₂[j - l₁.length]'(by rw [List.length_append] at hj; omega)) g) :
    Rep 11200 (l₁ ++ l₂)[j] g := by
  rw [List.getElem_append_right h]
  exact hr

theorem syH_rep : ∀ j (hj : j < harWgens.length), Rep 11200 harWgens[j] (syH j) := by
  intro j hj
  have hj7 : j < 7 := by rwa [syW_len] at hj
  by_cases h5 : j < 5
  · exact rep_append_left (l₁ := harCgens) (l₂ := [tU [1], tU [2, 3, 3]])
      (by rw [syC_len]; exact h5) hj (syC_rep j _)
  · refine rep_append_right (l₁ := harCgens) (l₂ := [tU [1], tU [2, 3, 3]])
      (by rw [syC_len]; omega) hj ?_
    rcases (by omega : j = 5 ∨ j = 6) with rfl | rfl
    · simp only [syC_len, Nat.sub_self, List.getElem_cons_zero]
      have e : syH 5 = syU [1] := rfl
      rw [e]
      exact syU_rep (by decide)
    · simp only [syC_len, Nat.reduceSub, List.getElem_cons_succ, List.getElem_cons_zero]
      have e : syH 6 = syU [2, 3, 3] := rfl
      rw [e]
      exact syU_rep (by decide)

theorem sy_img {gs : List Table} {H : Nat → Equiv.Perm (Fin 11200)}
    (h : ∀ j (hj : j < gs.length), Rep 11200 gs[j] (H j)) :
    tp 11200 '' {x | x ∈ gs.toArray} = H '' {l | l < gs.length} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ gs := by simpa using hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
    exact ⟨j, hj, rep_unique (h j hj) (rep_tp (CFSG.KC.BfsPairs.permOK_of_rep (h j hj)))⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨gs[j], by simp, rep_unique (rep_tp (CFSG.KC.BfsPairs.permOK_of_rep (h j hj))) (h j hj)⟩

theorem syW_gen : genOf 11200 harWgens = Subgroup.closure (syH '' {l | l < 7}) := by
  unfold genOf
  rw [sy_img syH_rep, syW_len]

theorem syC_gen : genOf 11200 harCgens = Subgroup.closure (syH '' {l | l < 5}) := by
  unfold genOf
  rw [sy_img syC_rep, syC_len]

theorem syU_gen : genOf 11200 harU = Subgroup.closure (syG '' {l | l < 3}) := by
  unfold genOf
  rw [sy_img (H := syG) (fun j hj => by
    have h3 : j < 3 := by rwa [syU_len] at hj
    have hr := rep_tp (sy_perm_harU _ (syU_getD_mem h3))
    rw [List.getD_eq_getElem _ _ hj] at hr
    unfold syG
    rw [if_pos h3, List.getD_eq_getElem _ _ hj]
    exact hr), syU_len]

theorem sy_list_set {P Par Lab PI : Nat → Nat} {ng m : Nat} (hm : 0 < m)
    (htr : allN m (syTreeAt P Par Lab ng) = true) (hcl : allN m (syClosedAt P PI ng m) = true)
    (hiv : allN 1024 (syInvAt P PI m) = true) :
    (∀ i < m, r32 P i < 1024 ∧ r32 PI (r32 P i) = i) ∧
    (∀ q < 1024, r32 PI q < m → r32 P (r32 PI q) = q) ∧
    (Subgroup.closure (syH '' {l | l < ng}) : Set (Equiv.Perm (Fin 11200))) =
      (fun i => syE (r32 P i)) '' {i | i < m} := by
  have hc : ∀ i < m, r32 P i < 1024 ∧ r32 PI (r32 P i) = i ∧
      ∀ l < ng, r32 PI (syWalk l (r32 P i)) < m := by
    intro i hi
    have h := allN_spec hcl i hi
    unfold syClosedAt at h
    simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2, fun l hl => ?_⟩
    have h4 := allN_spec h3 l hl
    try simp only [CFSG.KS.PEnum.strictB_app'] at h4
    exact Nat.le_of_ble_eq_true h4
  have hv : ∀ q < 1024, r32 PI q < m → r32 P (r32 PI q) = q := by
    intro q hq he
    have h := allN_spec hiv q hq
    unfold syInvAt at h
    simp only [CFSG.KS.PEnum.strictB_app'] at h
    have hb : Nat.blt (r32 PI q) m = true := Eq.mpr Nat.blt_eq he
    rw [hb] at h
    exact Nat.eq_of_beq_eq_true h
  refine ⟨fun i hi => ⟨(hc i hi).1, (hc i hi).2.1⟩, hv, ?_⟩
  have h0 : r32 P 0 = 0 := by
    have h := allN_spec htr 0 hm
    exact Nat.eq_of_beq_eq_true h
  refine closure_eq_of_tree (by simp only [h0, syE_zero]) hm (fun i hi hi0 => ?_)
    (fun i hi l hl => ?_)
  · have h := allN_spec htr i hi
    unfold syTreeAt at h
    have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h' => hi0 (Nat.eq_of_beq_eq_true h')
    rw [e] at h
    simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hp : r32 Par i < i := Nat.le_of_ble_eq_true h1
    refine ⟨r32 Par i, hp, r32 Lab i, Nat.le_of_ble_eq_true h2, ?_⟩
    rw [← Nat.eq_of_beq_eq_true h3]
    exact (syWalk_eq _ (hc _ (by omega)).1).2
  · obtain ⟨hq, -, hw⟩ := hc i hi
    have hw' := syWalk_eq l hq
    exact ⟨_, hw l hl, by rw [hv _ hw'.1 (hw l hl), hw'.2]⟩

theorem sy_list_inj {P PI : Nat → Nat} {m : Nat}
    (h : ∀ i < m, r32 P i < 1024 ∧ r32 PI (r32 P i) = i) :
    ∀ i < m, ∀ j < m, syE (r32 P i) = syE (r32 P j) → i = j := by
  intro i hi j hj e
  have := congrArg (r32 PI) (syE_inj (h i hi).1 (h j hj).1 e)
  rwa [(h i hi).2, (h j hj).2] at this

theorem sy_card {H : Subgroup (Equiv.Perm (Fin 11200))} {f : Nat → Equiv.Perm (Fin 11200)}
    {m : Nat} (hS : (H : Set (Equiv.Perm (Fin 11200))) = f '' {i | i < m})
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) (p : Equiv.Perm (Fin 11200) → Prop)
    (b : Nat → Bool) (hb : ∀ i < m, b i = true ↔ p (f i)) :
    Nat.card {y : H // p y} = cntK m b := by
  rw [← card_eq_cntK hS hinj p b hb]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ H) p)

theorem sy_card_all {H : Subgroup (Equiv.Perm (Fin 11200))} {f : Nat → Equiv.Perm (Fin 11200)}
    {m : Nat} (hS : (H : Set (Equiv.Perm (Fin 11200))) = f '' {i | i < m})
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) : Nat.card H = m := by
  have h := sy_card hS hinj (fun _ => True) (fun _ => true) (fun _ _ => by simp)
  rw [CFSG.KC.PosWalk.cntK_eq, List.filter_true, List.length_range] at h
  rw [← h]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)).symm

theorem syCP : (∀ i < 128, r32 CPos i < 1024 ∧ r32 CPI (r32 CPos i) = i) ∧
    (∀ q < 1024, r32 CPI q < 128 → r32 CPos (r32 CPI q) = q) ∧
    (Subgroup.closure (syH '' {l | l < 5}) : Set (Equiv.Perm (Fin 11200))) =
      (fun i => syE (r32 CPos i)) '' {i | i < 128} :=
  sy_list_set (by norm_num) ch26131_treeC ch26131_clC ch26131_invC

theorem syWP : (∀ i < 512, r32 WPos i < 1024 ∧ r32 WPI (r32 WPos i) = i) ∧
    (∀ q < 1024, r32 WPI q < 512 → r32 WPos (r32 WPI q) = q) ∧
    (Subgroup.closure (syH '' {l | l < 7}) : Set (Equiv.Perm (Fin 11200))) =
      (fun i => syE (r32 WPos i)) '' {i | i < 512} :=
  sy_list_set (by norm_num) ch26131_treeW ch26131_clW ch26131_invW

theorem syC_set : (genOf 11200 harCgens : Set (Equiv.Perm (Fin 11200))) =
    (fun i => syE (r32 CPos i)) '' {i | i < 128} := by
  rw [syC_gen]
  exact syCP.2.2

theorem syW_set : (genOf 11200 harWgens : Set (Equiv.Perm (Fin 11200))) =
    (fun i => syE (r32 WPos i)) '' {i | i < 512} := by
  rw [syW_gen]
  exact syWP.2.2

theorem sy_pts : syT < 1024 ∧ syZ1 < 1024 ∧ syZ2 < 1024 ∧ syMul syT syT = 0 ∧
    syMul syZ1 syZ1 = 0 ∧ syT ≠ 0 ∧ syZ1 ≠ 0 ∧ syZ2 ≠ 0 ∧ syZ1 ≠ syT ∧ syZ2 ≠ syT ∧
    syZ2 ≠ syZ1 := by
  have h := ch26131_pts
  simp only [bAnd_iff, bIf_ft, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.ne_of_beq_eq_false h6,
    Nat.ne_of_beq_eq_false h7, Nat.ne_of_beq_eq_false h8, Nat.ne_of_beq_eq_false h9,
    Nat.ne_of_beq_eq_false h10, Nat.ne_of_beq_eq_false h11⟩

theorem syT_rep : Rep 11200 harC0 (syE syT) := by
  have e : syE syT = syU [1, 2, 1, 2, 3, 1, 2, 1, 2, 3] := by
    rw [syT, (sy_walk (by decide) (by norm_num : (0 : Nat) < 1024)).2, syE_zero, one_mul]
    rfl
  rw [e]
  exact syU_rep (by decide)

theorem syZ1_rep : Rep 11200 harZ1 (syE syZ1) := by
  have e : syE syZ1 = syU [3, 3, 3, 3] := by
    rw [syZ1, (sy_walk (by decide) (by norm_num : (0 : Nat) < 1024)).2, syE_zero, one_mul]
    rfl
  rw [e]
  exact syU_rep (by decide)

theorem syZ2_eq : syE syZ2 = syE syT * syE syZ1 := by
  have e : syE syZ1 = ([2, 2, 2, 2].map syG).prod := by
    rw [syZ1, (sy_walk (by decide) (by norm_num : (0 : Nat) < 1024)).2, syE_zero, one_mul]
  rw [syZ2, (sy_walk (by decide) sy_pts.1).2, e]

theorem syZ2_rep : Rep 11200 harZ2 (syE syZ2) := by
  rw [syZ2_eq]
  exact Rep.compT syT_rep syZ1_rep

theorem sy_sq_iff {x z : Nat} (hx : x < 1024) (hz : z < 1024) :
    Nat.beq (syMul x x) z = true ↔ syE x ^ 2 = syE z := by
  obtain ⟨h1, h2⟩ := syMul_eq hx hx
  rw [Nat.beq_eq, ← syE_eq_iff h1 hz, h2, pow_two]

theorem sy_cnt_T0 {z : Nat} (hz : z < 1024) :
    Nat.card {y : genOf 11200 harU // (y : Equiv.Perm (Fin 11200)) ^ 2 = syE z} = sySqCntE z :=
  sy_card sy_T0_set (fun i hi j hj => syE_inj hi hj) (fun y => y ^ 2 = syE z)
    (fun x => Nat.beq (syMul x x) z) (fun x hx => sy_sq_iff hx hz)

theorem sy_cnt_C {z : Nat} (hz : z < 1024) :
    Nat.card {y : genOf 11200 harCgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = syE z} =
      sySqCnt CPos 128 z :=
  sy_card syC_set (sy_list_inj syCP.1) (fun y => y ^ 2 = syE z)
    (fun i => strictB (r32 CPos i) (fun x => Nat.beq (syMul x x) z)) (fun i hi => by
    rw [CFSG.KS.PEnum.strictB_app']
    exact sy_sq_iff (syCP.1 i hi).1 hz)

theorem sy_cnt_W {z : Nat} (hz : z < 1024) :
    Nat.card {y : genOf 11200 harWgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = syE z} =
      sySqCnt WPos 512 z :=
  sy_card syW_set (sy_list_inj syWP.1) (fun y => y ^ 2 = syE z)
    (fun i => strictB (r32 WPos i) (fun x => Nat.beq (syMul x x) z)) (fun i hi => by
    rw [CFSG.KS.PEnum.strictB_app']
    exact sy_sq_iff (syWP.1 i hi).1 hz)

theorem mem_centralizer_closure_iff {M : Type*} [Group M] {s : Set M} {g : M} :
    g ∈ Subgroup.centralizer (Subgroup.closure s : Set M) ↔ ∀ h ∈ s, h * g = g * h := by
  constructor
  · intro hg h hh
    exact (Subgroup.mem_centralizer_iff.1 hg) h (Subgroup.subset_closure hh)
  · intro H
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : Subgroup.closure s ≤ Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      intro k hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact H k hk
    have := hle hh
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this

theorem sy_comm_iff {x : Nat} (hx : x < 1024) {j : Nat} (hj : j < 3) :
    Nat.beq (wstepK TECl 6 x j) (syMul (wstepK TECl 6 0 j) x) = true ↔
      syG j * syE x = syE x * syG j := by
  obtain ⟨a1, a2⟩ := sy_hcl x hx j (by omega)
  obtain ⟨b1, b2⟩ := sy_hcl 0 (by norm_num) j (by omega)
  obtain ⟨c1, c2⟩ := syMul_eq b1 hx
  rw [Nat.beq_eq, ← syE_eq_iff a1 c1, a2, c2, b2, syE_zero, one_mul, eq_comm]

theorem sy_centre : Nat.card ↥(genOf 11200 harU ⊓
    Subgroup.centralizer (genOf 11200 harU : Set (Equiv.Perm (Fin 11200)))) = 4 := by
  have hc := card_eq_cntK sy_T0_set (fun i hi j hj => syE_inj hi hj)
    (fun y => y ∈ Subgroup.centralizer (genOf 11200 harU : Set (Equiv.Perm (Fin 11200))))
    (fun x => allN 3 (fun j => Nat.beq (wstepK TECl 6 x j) (syMul (wstepK TECl 6 0 j) x)))
    (fun x hx => by
      rw [Raw.Orb.allN_iff, syU_gen, mem_centralizer_closure_iff]
      constructor
      · rintro H _ ⟨j, hj, rfl⟩
        exact (sy_comm_iff hx hj).1 (H j hj)
      · intro H j hj
        exact (sy_comm_iff hx hj).2 (H _ ⟨j, hj, rfl⟩))
  rw [Nat.eq_of_beq_eq_true ch26131_cent] at hc
  rw [← hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Subgroup.mem_inf)

theorem sy_inv {y : Equiv.Perm (Fin 11200)} (hy : y ∈ genOf 11200 harU) (hy2 : y ^ 2 = 1) :
    y ∈ genOf 11200 harWgens := by
  obtain ⟨x, hx, rfl⟩ := syE_cover hy
  have h0 : syMul x x = 0 := by
    have := (sy_sq_iff hx (by norm_num : (0 : Nat) < 1024)).2 (by rw [hy2, syE_zero])
    exact Nat.eq_of_beq_eq_true this
  have h : bIf(Nat.beq (syMul x x) 0, Nat.blt (r32 WPI x) 512, true) = true :=
    allN_spec ch26131_inv x hx
  rw [h0] at h
  have h' : Nat.blt (r32 WPI x) 512 = true := h
  have hw : r32 WPI x < 512 := Nat.le_of_ble_eq_true h'
  have hm : syE x ∈ (genOf 11200 harWgens : Set (Equiv.Perm (Fin 11200))) := by
    rw [syW_set]
    refine ⟨r32 WPI x, hw, ?_⟩
    change syE (r32 WPos (r32 WPI x)) = syE x
    rw [syWP.2.1 x hx hw]
  exact hm

end CFSG.KD.TwoHS

end
