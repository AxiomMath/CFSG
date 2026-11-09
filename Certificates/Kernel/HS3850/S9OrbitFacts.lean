module

public import Certificates.Kernel.HS3850.S9OrbitK
public import Certificates.Kernel.HS3850.FusFacts
public import CFSG.Certificates.Kernel.EvenSporDS81.FCSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850.S9

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KS.MulH
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Recognition.HSMultiplier CertificateChecks.KernelSporSch
open CFSG.KD.LQT.HO (Cn)
open CFSG.KD.HS3850 (hid hidc compT_pc cn_pc)

private theorem let_ok (i : Nat) (hi : i < 2) :
    Cn (PHSC.S i) ∧ Cn (PHSC.SI i) ∧
      invEqK 3850 12 (mask 12) (3850 * 12) (PHSC.S i) (PHSC.SI i) = true := by
  have h := List.all_eq_true.1 kLet i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem tab2_get0 (a b : Table) : (#[a, b] : Array Table)[0]! = a := rfl
private theorem tab2_get1 (a b : Table) : (#[a, b] : Array Table)[1]! = b := rfl
private theorem map_tabT (a : Array Nat) : a.map UInt32.ofNat = tabT a := rfl
private theorem tabm2_get0 (a b : Table) :
    ((#[a, b] : Array Table).map (invT 3850))[0]! = invT 3850 a := by
  rw [List.map_toArray, List.map_cons, List.map_cons, List.map_nil, tab2_get0]
private theorem tabm2_get1 (a b : Table) :
    ((#[a, b] : Array Table).map (invT 3850))[1]! = invT 3850 b := by
  rw [List.map_toArray, List.map_cons, List.map_cons, List.map_nil, tab2_get1]

private theorem harA_tab (i : Fin 2) : harA i = tabT (unpack 3850 12 (PHSC.S i.val)) := by
  have e : harA i = tabT (CFSG.Sporadic.Schreier.hsStrongArrs[i.val]!) := by
    unfold harA
    rw [hsPGTbls.eq_1]
    fin_cases i
    · rw [show ((⟨0, by decide⟩ : Fin 2) : Nat) = 0 from rfl, tab2_get0, map_tabT]
    · rw [show ((⟨1, by decide⟩ : Fin 2) : Nat) = 1 from rfl, tab2_get1, map_tabT]
  rw [e, PHSCheck.arr_eq i.val (by omega)]

private theorem harAI_tab (i : Fin 2) : harAI i = tabT (unpack 3850 12 (PHSC.SI i.val)) := by
  have e : harAI i = invT 3850 (harA i) := by
    unfold harAI harA
    rw [hsPGInvTbls.eq_1, hsPGTbls.eq_1]
    fin_cases i
    · rw [show ((⟨0, by decide⟩ : Fin 2) : Nat) = 0 from rfl, tabm2_get0, tab2_get0]
    · rw [show ((⟨1, by decide⟩ : Fin 2) : Nat) = 1 from rfl, tabm2_get1, tab2_get1]
  rw [e, harA_tab, invT_unpack (by norm_num) (let_ok i.val i.2).2.2]

private theorem foldl_tab {α : Type} (f : α → Table) (S : α → Nat) :
    ∀ (wd : List α) (acc : Nat) (init : Table), init = tabT (unpack 3850 12 acc) → Cn acc →
      (∀ l ∈ wd, f l = tabT (unpack 3850 12 (S l)) ∧ Cn (S l)) →
      wd.foldl (fun a l => compT 3850 a (f l)) init =
          tabT (unpack 3850 12 (wd.foldl (fun a l => pc a (S l)) acc)) ∧
        Cn (wd.foldl (fun a l => pc a (S l)) acc)
  | [], acc, init, hi, ha, _ => by
    rw [List.foldl_nil, List.foldl_nil, hi]
    exact ⟨rfl, ha⟩
  | l :: wd, acc, init, hi, ha, h => by
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_tab f S wd (pc acc (S l)) _ (by rw [hi, h1, compT_pc ha h2]) (cn_pc ha h2)
      fun l' hl' => h l' (List.mem_cons_of_mem l hl')

private theorem letter_tab (l : Fin 2 × Bool) :
    (if l.2 then harA l.1 else harAI l.1) = tabT (unpack 3850 12 (letK l)) ∧ Cn (letK l) := by
  obtain ⟨c1, c2, -⟩ := let_ok l.1.val l.1.2
  unfold letK
  cases l.2
  · exact ⟨harAI_tab l.1, c2⟩
  · exact ⟨harA_tab l.1, c1⟩

private theorem harX_tab (i : Fin 6) : harX i = tabT (unpack 3850 12 (HX i.val)) ∧ Cn (HX i.val) := by
  unfold harX evalW HX
  exact foldl_tab _ letK _ _ _ hid hidc fun l _ => letter_tab l

private theorem harXs_getD {g : Nat} (hg : g < 6) :
    harXs.getD g (idT 3850) = tabT (unpack 3850 12 (HX g)) ∧ Cn (HX g) := by
  have e : harXs.getD g (idT 3850) = harX ⟨g, hg⟩ := by
    rw [harXs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_finRange]
    rfl
  rw [e]
  exact harX_tab ⟨g, hg⟩

private theorem piBeta_tab {j : Nat} (hj : j < 3) :
    piBetaT j = tabT (unpack 3850 12 (B j)) ∧ Cn (B j) := by
  have hw : ∀ l ∈ betaWords.getD j [], l - 1 < 6 := by
    interval_cases j <;> decide
  unfold piBetaT wordTbl B
  exact foldl_tab _ (fun l => HX (l - 1)) _ _ _ hid hidc fun l hl => harXs_getD (hw l hl)

private theorem piBetaSq_tab {j : Nat} (hj : j < 3) : piBetaSqT j = tabT (unpack 3850 12 (BSQ j)) := by
  obtain ⟨h1, c1⟩ := piBeta_tab hj
  unfold piBetaSqT BSQ
  rw [h1, compT_pc c1 c1]

private theorem ap_tab (X p : Nat) : ap (tabT (unpack 3850 12 X)) p = imgK X p := by
  unfold imgK
  by_cases hp : p < 3850
  · rw [if_pos hp, ap_tabT _ (by
      rw [CFSG.KS.Raw.Orb.unpack_get hp]
      exact (CFSG.KS.PF.pg_lt 12 X p).trans (by norm_num)), CFSG.KS.Raw.Orb.unpack_get hp]
    rfl
  · rw [if_neg hp]
    unfold ap
    rw [tabT_get]
    have hs : (unpack 3850 12 X).size = 3850 := by simp [unpack]
    rw [getElem!_neg _ _ (by omega)]
    rfl

private theorem sigma_eq : sigmaPts = sigmaC := by
  unfold sigmaPts sigmaC
  apply List.filter_congr
  intro p _
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  rw [piBetaSq_tab (List.mem_range.1 hj), ap_tab]

private theorem steps_eq : orbitSteps = stepsC := by
  unfold orbitSteps stepsC
  rw [S9T.eq, show (" " : String) = String.singleton ' ' from rfl,
    CFSG.KC.Str.splitOn_ofList, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ds hds
  have h := List.all_eq_true.1 kDigits ds hds
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
  exact CFSG.KC.Str.toNat!_ofList h.1 h.2

private theorem step_at {j : Nat} (hj : j < stepsC.length) :
    stepsC[j] = (par (j + 1), gen (j + 1)) ∧ par (j + 1) ≤ j ∧ gen (j + 1) < 6 := by
  have h := List.all_eq_true.1 kSteps.2 (stepsC[j], j) (by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simpa using hj, by simp⟩)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨Prod.ext h1 h2, h1 ▸ h3, h2 ▸ h4⟩

private theorem par_lt {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 4124) : par k < k := by
  obtain ⟨-, h, -⟩ := step_at (j := k - 1) (by rw [kSteps.1]; omega)
  rw [show k - 1 + 1 = k by omega] at h
  omega

private theorem ptK_fuel (x : Nat) : ∀ k, k ≤ 4124 → ∀ f g, k ≤ f → k ≤ g →
    ptK f k x = ptK g k x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk f g hf hg
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      cases f <;> cases g <;> rfl
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hp := par_lt h0 hk
      simp only [ptK, show k ≠ 0 by omega, ↓reduceIte, CFSG.KS.PF.strictN_eqP]
      rw [ih (par k) hp (by omega) f' g' (by omega) (by omega)]

private theorem ptK_succ (x : Nat) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) :
    ptK m m x = imgK (HX (gen m)) (ptK (par m) (par m) x) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp := par_lt h1 h2
  simp only [ptK, show m' + 1 ≠ 0 by omega, ↓reduceIte, CFSG.KS.PF.strictN_eqP]
  rw [ptK_fuel x (par (m' + 1)) (by omega) m' (par (m' + 1)) (by omega) le_rfl]

private theorem setC_succ {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) :
    setC m = (setC (par m)).map (imgK (HX (gen m))) := by
  rw [setC, setC, List.map_map]
  exact List.map_congr_left fun x _ => ptK_succ x h1 h2

private theorem s9Eq_spec {X b c : Nat} (h : s9Eq X b c = true) :
    s9Dec b = (s9Dec c).map (imgK X) := by
  simp only [s9Eq, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  simp only [s9Dec, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact h

private theorem s9Lt_spec (b : Nat) : s9Lt b = (s9Dec b).all (· < 3850) := by
  simp only [s9Lt, s9Dec, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

private theorem s9MaskN_eq (b : Nat) : s9MaskN b = s9Mask (s9Dec b) := rfl

private theorem s9Step_one {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) : s9Step m = 1 := by
  have key : ∀ s n, ((List.range' s n).all fun k => s9Step k == 1) = true → s ≤ m →
      m < s + n → s9Step m = 1 := fun s n h hs hm => by
    have := List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨hs, hm⟩)
    simpa using this
  by_cases a : m < 689
  · exact key 1 688 kSets0 h1 (by omega)
  by_cases b : m < 1377
  · exact key 689 688 kSets1 (by omega) (by omega)
  by_cases c : m < 2065
  · exact key 1377 688 kSets2 (by omega) (by omega)
  by_cases d : m < 2753
  · exact key 2065 688 kSets3 (by omega) (by omega)
  by_cases e : m < 3441
  · exact key 2753 688 kSets4 (by omega) (by omega)
  exact key 3441 684 kSets5 (by omega) (by omega)

private theorem s9Set_step {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) :
    s9Set m = (s9Set (par m)).map (imgK (HX (gen m))) := by
  have hs := s9Step_one h1 h2
  simp only [s9Step, CFSG.KS.PF.strictN_eqP] at hs
  have he : s9Eq (HX (gen m)) (s9Blk m) (s9Blk (par m)) = true := by
    by_contra hne
    simp [hne] at hs
  exact s9Eq_spec he

private theorem s9Set_eq : ∀ k, k ≤ 4124 → s9Set k = setC k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have h := kSigma
      rw [beq_iff_eq] at h
      have e : ptK 0 0 = id := rfl
      rw [h, setC, e, List.map_id]
    · have hp := par_lt h0 hk
      rw [s9Set_step h0 hk, setC_succ h0 hk, ih (par k) hp (by omega)]

private noncomputable def arrM (m : Nat) : Array (List Nat) := ((List.range m).map setC).toArray

private theorem arrM_size (m : Nat) : (arrM m).size = m := by
  rw [arrM, List.size_toArray, List.length_map, List.length_range]

private theorem arrM_get {m p : Nat} (hp : p < (arrM m).size) : (arrM m)[p] = setC p := by
  simp only [arrM, List.getElem_toArray, List.getElem_map, List.getElem_range]

private theorem img_new {m p g : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) (hpar : par m = p)
    (hgen : gen m = g) (hg : g < 6) : imgList (harXs.getD g (idT 3850)) (setC p) = setC m := by
  have hx : ∀ x, ap (harXs.getD g (idT 3850)) (ptK p p x) = ptK m m x := fun x => by
    rw [(harXs_getD hg).1, ap_tab, ptK_succ x h1 h2, hpar, hgen]
  have e1 : imgList (harXs.getD g (idT 3850)) (setC p) =
      sigmaC.map (fun x => ap (harXs.getD g (idT 3850)) (ptK p p x)) := by
    rw [imgList.eq_1, setC.eq_1, List.map_map]
    rfl
  rw [e1, setC.eq_1]
  exact List.map_congr_left fun x _ => hx x

private theorem arrM_push (m : Nat) : (arrM m).push (setC m) = arrM (m + 1) := by
  rw [arrM, arrM, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.push_toArray]

private theorem step_m {m p g : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 4124) (hpar : par m = p)
    (hgen : gen m = g) (hp : p < m) (hg : g < 6) :
    orbitStep (some (arrM m)) (p, g) = some (arrM (m + 1)) := by
  have hc : (p, g).1 < (arrM m).size ∧ (p, g).2 < 6 := ⟨by rw [arrM_size]; exact hp, hg⟩
  have hget := arrM_get (m := m) hc.1
  have hnew := img_new h1 h2 hpar hgen hg
  have hpush := arrM_push m
  unfold orbitStep
  dsimp only
  rw [dif_pos hc]
  rw [hget, hnew, hpush]

private theorem fold_m : ∀ (L : List (Nat × Nat)) (m : Nat), 1 ≤ m → m + L.length ≤ 4125 →
    (∀ i (hi : i < L.length), L[i] = (par (m + i), gen (m + i)) ∧ par (m + i) < m + i ∧
      gen (m + i) < 6) →
    L.foldl orbitStep (some (arrM m)) = some (arrM (m + L.length))
  | [], m, _, _, _ => rfl
  | st :: L, m, h1, h2, h => by
    obtain ⟨e, hp, hg⟩ := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at e hp hg
    have e1 : par m = st.1 := by rw [e]
    have e2 : gen m = st.2 := by rw [e]
    rw [List.foldl_cons, step_m (p := st.1) (g := st.2) h1 (by simp at h2; omega) e1 e2
      (e1 ▸ hp) (e2 ▸ hg)]
    have := fold_m L (m + 1) (by omega) (by simp at h2; omega) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rwa [show m + (i + 1) = m + 1 + i by omega] at this
    rw [this]
    simp only [List.length_cons]
    congr 2
    omega

private theorem sets_eq : orbitSets = some (arrM 4125) := by
  have h0 : (#[sigmaPts] : Array (List Nat)) = arrM 1 := by
    rw [sigma_eq]
    simp only [arrM, List.range_one, List.map_cons, List.map_nil, setC]
    have : sigmaC.map (ptK 0 0) = sigmaC := by
      rw [show ptK 0 0 = id from rfl, List.map_id]
    rw [this]
  unfold orbitSets
  rw [h0, steps_eq]
  have hl := kSteps.1
  rw [fold_m stepsC 1 le_rfl (by omega) fun i hi => by
    obtain ⟨a, b, c⟩ := step_at hi
    rw [show 1 + i = i + 1 by omega]
    exact ⟨a, by omega, c⟩, hl]

private theorem mergeK_perm : ∀ (f : Nat) (a b : List Nat), (mergeK f a b).Perm (a ++ b)
  | 0, a, b => by simp [mergeK]
  | f + 1, [], b => by simp [mergeK]
  | f + 1, x :: a, [] => by simp [mergeK]
  | f + 1, x :: a, y :: b => by
    simp only [mergeK]
    split
    · exact (mergeK_perm f a (y :: b)).cons x
    · exact ((mergeK_perm f (x :: a) b).cons y).trans List.perm_middle.symm

private theorem mergePairsK_perm : ∀ L : List (List Nat), (mergePairsK L).flatten.Perm L.flatten
  | a :: b :: L => by
    simp only [mergePairsK, List.flatten_cons]
    rw [← List.append_assoc]
    exact (mergeK_perm 8192 a b).append (mergePairsK_perm L)
  | [] => by simp [mergePairsK]
  | [a] => by simp [mergePairsK]

private theorem flatten_singletons : ∀ l : List Nat, (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.flatten_cons, flatten_singletons l, List.singleton_append]

private theorem msortK_perm (l : List Nat) : (msortK l).Perm l := by
  have key : ∀ n, (Nat.rec (motive := fun _ => List (List Nat)) (l.map fun x => [x])
      (fun _ L => mergePairsK L) n : List (List Nat)).flatten.Perm l := by
    intro n
    induction n with
    | zero =>
      change (l.map fun x => [x]).flatten.Perm l
      rw [flatten_singletons]
    | succ n ih => exact (mergePairsK_perm _).trans ih
  exact key 13

private theorem strict_head : ∀ (a : Nat) (l : List Nat), strictlyIncreasing (a :: l) = true →
    ∀ x ∈ l, a < x
  | _, [], _, x, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (strict_head b l h.2 x hx)

private theorem strict_tail : ∀ (a : Nat) (l : List Nat), strictlyIncreasing (a :: l) = true →
    strictlyIncreasing l = true
  | _, [], _ => rfl
  | a, b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true] at h
    exact h.2

private theorem strict_pairwise : ∀ l : List Nat, strictlyIncreasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | a :: l, h => List.Pairwise.cons (strict_head a l h) (strict_pairwise l (strict_tail a l h))

private theorem pairwise_strict : ∀ l : List Nat, l.Pairwise (· < ·) →
    strictlyIncreasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, pairwise_strict (b :: l) h.of_cons⟩

private theorem testBit_s9Mask (p : Nat) : ∀ l : List Nat, (s9Mask l).testBit p = true ↔ p ∈ l
  | [] => by simp [s9Mask]
  | a :: l => by
    have ih := testBit_s9Mask p l
    simp only [s9Mask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

private theorem s9Mask_congr {l l' : List Nat} (h : ∀ p, p ∈ l ↔ p ∈ l') :
    s9Mask l = s9Mask l' :=
  Nat.eq_of_testBit_eq fun p => by
    rw [Bool.eq_iff_iff, testBit_s9Mask, testBit_s9Mask]
    exact h p

private theorem keyDigits_inj (l : List Nat) : ∀ l' : List Nat, l.Pairwise (· < ·) →
    l'.Pairwise (· < ·) → (∀ x ∈ l, x < 4096) → (∀ x ∈ l', x < 4096) → l ≠ [] → l' ≠ [] →
    l.foldr (fun p acc => p + 4096 * acc) 0 = l'.foldr (fun p acc => p + 4096 * acc) 0 →
    l = l' := by
  induction l with
  | nil => intro l' _ _ _ _ h; exact absurd rfl h
  | cons a r ih =>
    intro l' h1 h2 h3 h4 _ h6 he
    rcases l' with _ | ⟨b, r'⟩
    · exact absurd rfl h6
    simp only [List.foldr_cons] at he
    have ha := h3 a List.mem_cons_self
    have hb := h4 b List.mem_cons_self
    have hab : a = b := by omega
    have hr : r.foldr (fun p acc => p + 4096 * acc) 0 =
        r'.foldr (fun p acc => p + 4096 * acc) 0 := by omega
    subst hab
    rcases r with _ | ⟨c, s⟩ <;> rcases r' with _ | ⟨c', s'⟩
    · rfl
    · have hc := List.rel_of_pairwise_cons h2 List.mem_cons_self
      simp only [List.foldr_cons, List.foldr_nil] at hr
      omega
    · have hc := List.rel_of_pairwise_cons h1 List.mem_cons_self
      simp only [List.foldr_cons, List.foldr_nil] at hr
      omega
    · rw [ih (c' :: s') h1.of_cons h2.of_cons (fun x hx => h3 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h4 x (List.mem_cons_of_mem _ hx)) (List.cons_ne_nil _ _)
        (List.cons_ne_nil _ _) hr]

private theorem mask_of_key {l l' : List Nat} (hl : ∀ x ∈ l, x < 3850)
    (hl' : ∀ x ∈ l', x < 3850) (h0 : l ≠ []) (h0' : l' ≠ []) (h : setKey l = setKey l') :
    s9Mask l = s9Mask l' := by
  have hmem : ∀ m : List Nat, (∀ x ∈ m, x < 3850) → ∀ x, x ∈ canonList m ↔ x ∈ m := by
    intro m hm x
    unfold canonList
    rw [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hm x h, h⟩⟩
  have hpw : ∀ m : List Nat, (canonList m).Pairwise (· < ·) := fun m =>
    List.Pairwise.filter _ List.pairwise_lt_range
  have hlt : ∀ m : List Nat, ∀ x ∈ canonList m, x < 4096 := by
    intro m x hx
    unfold canonList at hx
    rw [List.mem_filter, List.mem_range] at hx
    have := hx.1
    omega
  have hne : ∀ m : List Nat, (∀ x ∈ m, x < 3850) → m ≠ [] → canonList m ≠ [] := by
    intro m hm h0m
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil m h0m
    exact List.ne_nil_of_mem ((hmem m hm x).2 hx)
  have hc := keyDigits_inj _ _ (hpw l) (hpw l') (hlt l) (hlt l') (hne l hl h0) (hne l' hl' h0') h
  exact s9Mask_congr fun p => by rw [← hmem l hl, ← hmem l' hl', hc]

theorem orbitOK_true : CFSG.EvenSporadicStandard.TwoHS.orbitOK = true := by
  unfold CFSG.EvenSporadicStandard.TwoHS.orbitOK
  rw [sets_eq]
  have hD : ∀ k ∈ List.range 4125, s9Set k = setC k := fun k hk =>
    s9Set_eq k (by rw [List.mem_range] at hk; omega)
  have e1 : ((List.range 4125).all fun k => (s9Set k).all (· < 3850)) =
      (List.range 4125).all fun k => (setC k).all (· < 3850) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h k hk
      rw [← hD k hk]
      exact h k hk
    · intro h k hk
      rw [hD k hk]
      exact h k hk
  have hOk : ((List.range 4125).all fun k => s9Ok k == 1) =
      (List.range 4125).all fun k => (s9Set k).all (· < 3850) := by
    congr 1
    funext k
    simp only [s9Ok, s9Set, CFSG.KS.PF.strictN_eqP, s9Lt_spec]
    split <;> simp_all
  have hKey : (List.range 4125).map s9Key = (List.range 4125).map fun k => s9Mask (setC k) := by
    refine List.map_congr_left fun k hk => ?_
    rw [← hD k hk]
    simp only [s9Key, s9Set, CFSG.KS.PF.strictN_eqP, s9MaskN_eq]
  have h : ((List.range 4125).all fun k => (setC k).all (· < 3850)) = true ∧
      strictlyIncreasing (msortK ((List.range 4125).map fun k => s9Mask (setC k))) = true := by
    have h1 := kOk
    have h2 := kKeys
    rw [hOk, e1] at h1
    rw [hKey] at h2
    exact ⟨h1, h2⟩
  have hA : ∀ k ∈ List.range 4125, ∀ x ∈ setC k, x < 3850 := by
    intro k hk x hx
    have h1 := List.all_eq_true.1 h.1 k hk
    simpa using List.all_eq_true.1 h1 x hx
  have hne : ∀ k ∈ List.range 4125, setC k ≠ [] := by
    intro k hk
    rw [← hD k hk]
    apply List.ne_nil_of_length_pos
    simp [s9Set, s9Dec]
  have hmN : ((List.range 4125).map fun k => s9Mask (setC k)).Nodup :=
    (msortK_perm _).nodup_iff.1 (strict_pairwise _ h.2).nodup
  have hkN : ((List.range 4125).map fun k => setKey (setC k)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    exact List.inj_on_of_nodup_map hmN hx hy
      (mask_of_key (hA x hx) (hA y hy) (hne x hx) (hne y hy) hxy)
  have hS : strictlyIncreasing (((List.range 4125).map fun k => setKey (setC k)).mergeSort
      (fun a b => decide (a ≤ b))) = true := by
    apply pairwise_strict
    have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      ((List.range 4125).map fun k => setKey (setC k))
    have hn := (List.mergeSort_perm _ (fun a b : Nat => decide (a ≤ b))).nodup_iff.2 hkN
    exact (hs.and hn).imp fun hab => by
      obtain ⟨h1, h2⟩ := hab
      simp only [decide_eq_true_eq] at h1
      omega
  dsimp only
  rw [arrM, List.all_toArray, List.toList_toArray, List.size_toArray, List.length_map,
    List.length_range, List.all_map, List.map_map, Function.comp_def, Function.comp_def,
    beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  exact ⟨h.1, hS⟩

end CFSG.KD.HS3850.S9
