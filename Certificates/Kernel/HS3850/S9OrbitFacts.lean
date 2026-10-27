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

private theorem dedupS_spec : ∀ l : List Nat, l.Pairwise (· ≤ ·) →
    (dedupS l).Pairwise (· < ·) ∧ ∀ x, x ∈ dedupS l ↔ x ∈ l
  | [], _ => ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | [a], _ => ⟨List.pairwise_singleton _ _, fun _ => Iff.rfl⟩
  | a :: b :: l, h => by
    obtain ⟨ih1, ih2⟩ := dedupS_spec (b :: l) (List.Pairwise.of_cons h)
    have hab : ∀ y ∈ b :: l, a ≤ y := fun y hy => (List.pairwise_cons.1 h).1 y hy
    unfold dedupS
    by_cases e : a = b
    · rw [if_pos e]
      refine ⟨ih1, fun x => ?_⟩
      rw [ih2, List.mem_cons (a := x) (b := a)]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · rw [e]
          exact List.mem_cons_self
        · exact hx
    · rw [if_neg e]
      refine ⟨List.Pairwise.cons (fun y hy => ?_) ih1, fun x => ?_⟩
      · have hy' := (ih2 y).1 hy
        have h1 := hab y hy'
        rcases List.mem_cons.1 hy' with rfl | hy''
        · omega
        · have h2 := (List.pairwise_cons.1 (List.Pairwise.of_cons h)).1 y hy''
          have h3 := hab b List.mem_cons_self
          omega
      · rw [List.mem_cons, ih2, List.mem_cons (b := a)]

private theorem canon_eq (l : List Nat) (hl : ∀ x ∈ l, x < 3850) :
    canonList l = dedupS (CFSG.KC.EvenSporDS81.isortN l) := by
  have hs : (CFSG.KC.EvenSporDS81.isortN l).Pairwise (· ≤ ·) := by
    rw [CFSG.KC.EvenSporDS81.isortN_eq]
    exact List.pairwise_insertionSort _ _
  obtain ⟨h1, h2⟩ := dedupS_spec _ hs
  have hp : (CFSG.KC.EvenSporDS81.isortN l).Perm l := by
    rw [CFSG.KC.EvenSporDS81.isortN_eq]
    exact List.perm_insertionSort _ _
  have h0 : (canonList l).Pairwise (· < ·) := by
    unfold canonList
    exact List.Pairwise.filter _ List.pairwise_lt_range
  have hmem : ∀ x, x ∈ canonList l ↔ x ∈ dedupS (CFSG.KC.EvenSporDS81.isortN l) := by
    intro x
    rw [h2, hp.mem_iff]
    unfold canonList
    rw [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hl x h, h⟩⟩
  have hperm : (canonList l).Perm (dedupS (CFSG.KC.EvenSporDS81.isortN l)) :=
    (List.perm_ext_iff_of_nodup h0.nodup h1.nodup).2 hmem
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (h0.imp le_of_lt) (h1.imp le_of_lt) hperm

private theorem setKey_eq (l : List Nat) (hl : ∀ x ∈ l, x < 3850) : setKey l = setKeyC l := by
  unfold setKey setKeyC
  rw [canon_eq l hl]

theorem orbitOK_true : CFSG.EvenSporadicStandard.TwoHS.orbitOK = true := by
  unfold CFSG.EvenSporadicStandard.TwoHS.orbitOK
  rw [sets_eq]
  have hK := kKeys
  have hA : ∀ k ∈ List.range 4125, ∀ x ∈ setC k, x < 3850 := by
    have hK' := hK
    rw [Bool.and_eq_true] at hK'
    intro k hk x hx
    have h1 := List.all_eq_true.1 hK'.1 k hk
    simpa using List.all_eq_true.1 h1 x hx
  have hmap : ((List.range 4125).map fun k => setKey (setC k)) =
      (List.range 4125).map fun k => setKeyC (setC k) :=
    List.map_congr_left fun k hk => setKey_eq _ (hA k hk)
  dsimp only
  rw [arrM, List.all_toArray, List.toList_toArray, List.size_toArray, List.length_map,
    List.length_range, List.all_map, List.map_map, Function.comp_def, Function.comp_def, hmap,
    CFSG.KC.EvenSporDS81.mergeSort_eq_isortN, beq_self_eq_true, Bool.true_and]
  exact hK

end CFSG.KD.HS3850.S9
