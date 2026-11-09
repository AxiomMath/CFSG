module

public import Certificates.Kernel.Sporadic.Fi24Sev.SevenB
public import Certificates.Kernel.Sporadic.Fi24KPerm.W0
public import Certificates.Kernel.Sporadic.Fi24KPerm.W1
public import Certificates.Kernel.Sporadic.Fi24KPerm.W2
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl0
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl1
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl2
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl3
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl4
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl5
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl6
public import Certificates.Kernel.Sporadic.Fi24KPerm.Sl7
public import Certificates.Kernel.Sporadic.Fi24KPerm.Fq
public import Certificates.Kernel.Sporadic.Fi24KPerm.Pt
public import Certificates.Kernel.Sporadic.Fi24Seven.Layout
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Orders.He.RelsBind
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Group

set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Final

open CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
open CFSG.Sporadic.Fi24 (J gs)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev
  CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.KD.Fi24Sev.Words CFSG.KD.Fi24Sev.SevenB CFSG.KC.SlpM
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

attribute [local instance] CFSG.Sporadic.Fi24.rAction

local notation "SL" => CFSG.KD.Fi24KPerm.sl

local notation "WE" => CFSG.KC.SlpM.appL CFSG.KD.F24S.W7 CFSG.KD.F24S.EK

#kc_forall_tree CFSG.KD.Fi24KPerm.Ck.slcAll (fun i => CFSG.KD.Fi24KPerm.slc i = true) 632
  CFSG.KD.Fi24KPerm.Ck.slc

#kc_forall_tree CFSG.KD.Fi24KPerm.Ck.fqcAll (fun i => CFSG.KD.Fi24KPerm.fqc i = true) 69
  CFSG.KD.Fi24KPerm.Ck.fqc

theorem flatMap_cuts {α : Type} (l : List α) (f : ℕ → ℕ) (h0 : f 0 = 0) :
    ∀ n, (∀ i < n, f i ≤ f (i + 1)) →
      (List.range n).flatMap (fun i => (l.drop (f i)).take (f (i + 1) - f i)) = l.take (f n)
  | 0, _ => by rw [h0]; rfl
  | n + 1, hf => by
    rw [List.range_succ, List.flatMap_append, flatMap_cuts l f h0 n (fun i hi => hf i (by omega)),
      List.flatMap_singleton, ← List.take_add, Nat.add_sub_cancel' (hf n (by omega))]

theorem cut_mono : ∀ i < 632, nthD 0 CFSG.KD.Fi24KPerm.slCut i ≤
    nthD 0 CFSG.KD.Fi24KPerm.slCut (i + 1) := by decide +kernel

theorem cut_len : List.length SL ≤ nthD 0 CFSG.KD.Fi24KPerm.slCut 632 := by decide +kernel

theorem sl_split : SL = (List.range 632).flatMap CFSG.KD.Fi24KPerm.slQ := by
  have h := flatMap_cuts SL (nthD 0 CFSG.KD.Fi24KPerm.slCut) (by decide +kernel) 632 cut_mono
  rw [List.take_of_length_le cut_len] at h
  exact h.symm

@[expose] noncomputable def wkPass (ws : List (List ℕ)) : ℕ → List (ℕ × List ℕ × List ℕ) → Bool :=
  List.rec (motive := fun _ => ℕ → List (ℕ × List ℕ × List ℕ) → Bool)
    (fun _ s => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) s)
    (fun w _ ih j s => List.rec (motive := fun _ => Bool) true
      (fun e s' _ => Bool.rec (motive := fun _ => Bool) (ih (Nat.succ j) s)
        ((decide (e.2.1 = w) && e.2.2.all fun l => decide (l < 26)) && ih (Nat.succ j) s')
        (Nat.beq e.1 j)) s) ws

theorem wkPass_spec : ∀ (ws : List (List ℕ)) (j : ℕ) (s : List (ℕ × List ℕ × List ℕ)),
    wkPass ws j s = true → ∀ e ∈ s, (∀ l ∈ e.2.2, l < 26) ∧ j ≤ e.1 ∧ e.1 < j + ws.length ∧
      ws.getD (e.1 - j) [] = e.2.1
  | [], _, [], _ => fun _ he => absurd he List.not_mem_nil
  | [], _, _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, _, [], _ => fun _ he => absurd he List.not_mem_nil
  | w :: ws, j, e :: s, h => by
    have up : ∀ x : ℕ × List ℕ × List ℕ, ((∀ l ∈ x.2.2, l < 26) ∧ j + 1 ≤ x.1 ∧
        x.1 < j + 1 + ws.length ∧ ws.getD (x.1 - (j + 1)) [] = x.2.1) →
        (∀ l ∈ x.2.2, l < 26) ∧ j ≤ x.1 ∧ x.1 < j + (w :: ws).length ∧
          (w :: ws).getD (x.1 - j) [] = x.2.1 := by
      intro x ⟨h1, h2, h3, h4⟩
      have hx : x.1 - j = (x.1 - (j + 1)) + 1 := by omega
      refine ⟨h1, by omega, by rw [List.length_cons]; omega, ?_⟩
      rw [hx, List.getD_cons_succ, h4]
    have h' : Bool.rec (motive := fun _ => Bool) (wkPass ws (j + 1) (e :: s))
        ((decide (e.2.1 = w) && e.2.2.all fun l => decide (l < 26)) && wkPass ws (j + 1) s)
        (Nat.beq e.1 j) = true := h
    cases hb : Nat.beq e.1 j with
    | false =>
      rw [hb] at h'
      exact fun x hx => up x (wkPass_spec ws (j + 1) (e :: s) h' x hx)
    | true =>
      rw [hb] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
      obtain ⟨⟨hw, hc⟩, hr⟩ := h'
      have he : e.1 = j := Nat.eq_of_beq_eq_true hb
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨hc, by omega, by rw [List.length_cons]; omega, ?_⟩
        rw [he, Nat.sub_self, List.getD_cons_zero, hw]
      · exact up x (wkPass_spec ws (j + 1) s hr x hx)

theorem we_len : (WE).length = 3820 := by
  rw [CFSG.KC.SlpM.appL_eq, List.length_append, CertificateChecks.KernelF24S.w7_len,
    CertificateChecks.KernelF24S.ek_len]

theorem wkPass_t : wkPass WE 0 SL = true := by decide +kernel

theorem sl_entry {e : ℕ × List ℕ × List ℕ} (he : e ∈ SL) :
    (∀ l ∈ e.2.2, l < 26) ∧ e.1 < 3820 ∧ (WE).getD e.1 [] = e.2.1 := by
  obtain ⟨h1, -, h3, h4⟩ := wkPass_spec _ _ _ wkPass_t e he
  rw [we_len, Nat.zero_add] at h3
  rw [Nat.sub_zero] at h4
  exact ⟨h1, h3, h4⟩

theorem sl_codes : ∀ e ∈ SL, ∀ l ∈ e.2.2, l < 26 := fun _ he => (sl_entry he).1

theorem sl_words : ∀ e ∈ SL, e.1 < 3820 ∧ (WE).getD e.1 [] = e.2.1 := fun _ he => (sl_entry he).2

theorem sl_spec : ∀ e ∈ SL,
    (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ SL, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU SL e.2.1) b = cP NW NT e.2.2 b := by
  intro e he
  rw [sl_split, List.mem_flatMap] at he
  obtain ⟨i, hi, h⟩ := he
  cases hq : orB (Nat.beq i 246) (Nat.beq i 247) with
  | true =>
    have hi' : i = 246 ∨ i = 247 := by
      rcases (orB_iff _ _).1 hq with e | e
      · exact Or.inl (Nat.eq_of_beq_eq_true e)
      · exact Or.inr (Nat.eq_of_beq_eq_true e)
    exact slIn_spec (CFSG.KD.Fi24KPerm.Ck.slPt hi') e h
  | false =>
    have hc := CFSG.KD.Fi24KPerm.Ck.slcAll i (List.mem_range.1 hi)
    unfold CFSG.KD.Fi24KPerm.slc at hc
    rw [hq] at hc
    dsimp only at hc
    rw [slInB_eq, brec_same] at hc
    exact slIn_spec hc e h

theorem WK_eq : WK = ((WE).map decW).toArray := by
  unfold WK
  rw [CertificateChecks.KernelF24S.words_eq, CertificateChecks.KernelF24S.extraK_eq,
    CertificateChecks.KernelF24S.layer_words]

theorem words_get {n : ℕ} (hn : n < 3820) : WK[n]! = decW ((WE).getD n []) := by
  rw [WK_eq, getElem!_pos _ n (by simp [we_len]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by rw [we_len]; omega)]

theorem words_eq (hB : Bridge) : ∀ e ∈ SL, wordElt e.2.2 = sK e.1 := by
  have key : ∀ n, ∀ e ∈ SL, e.1 = n → wordElt e.2.2 = sK n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e he hen
      obtain ⟨hz, hag⟩ := sl_spec e he
      obtain ⟨hn, hw⟩ := sl_words e he
      rw [← wordElt_eq_of_cb hB (expU_lt sl_codes _) (sl_codes e he) hag, wordElt_expU, sK,
        CFSG.Sporadic.Fi23.slpG_eq]
      rw [hen] at hn hw
      rw [words_get hn, hw]
      unfold wordG decW
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun z hzm => ?_
      obtain ⟨hz2, hz'⟩ := hz z hzm
      simp only [Function.comp]
      have habs : (decC z).natAbs = z / 2 := by
        unfold decC
        split_ifs
        · rw [Int.natAbs_neg, Int.natAbs_natCast]
        · rw [Int.natAbs_natCast]
      by_cases h5 : z ≤ 5
      · rw [letU_small h5, genG_letter z hz2 h5, ite_eq_left (by rw [habs]; omega)]
      · obtain ⟨hlt, e', he', he'k⟩ := hz'.resolve_left h5
        rw [hen] at hlt
        obtain ⟨e'', he'', he''k, hfu⟩ := findU_spec ⟨e', he', he'k⟩
        have hIH := ih _ hlt e'' he'' he''k
        rw [ite_eq_right (by rw [habs]; omega), habs, ite_eq_left hlt]
        unfold letU
        rw [ble_ne h5, lIf_false]
        have hsh : Nat.sub (Nat.shiftRight z 1) 3 = z / 2 - 3 := by
          simp [Nat.shiftRight_eq_div_pow]
        have hland : Nat.land z 1 = z % 2 := Nat.and_one_is_mod z
        rw [hsh, hfu, hland]
        by_cases hev : z % 2 = 0
        · have hd : decC z = ((z / 2 : ℕ) : ℤ) := by unfold decC; rw [ite_eq_right (by omega)]
          rw [beq_of hev, lIf_true, hIH, sK,
            ite_eq_left (by rw [hd]; exact_mod_cast (by omega : 0 < z / 2))]
        · have hd : decC z = -((z / 2 : ℕ) : ℤ) := by unfold decC; rw [ite_eq_left (by omega)]
          rw [beq_ne hev, lIf_false, wordElt_invC hB (sl_codes e'' he''), hIH, sK,
            ite_eq_right (by rw [hd]; omega)]
  exact fun e he => key e.1 e he rfl

@[expose] def roots : List ℕ :=
  [0, 1, 64, 66, 67, 1082, 1083, 1084, 1085, 1086, 1655, 1656, 2206, 2207, 2211, 2215, 2540, 2541,
    2542, 2546, 2550, 2806, 2807, 2808, 2812, 2816, 3078, 3079, 3080, 3084, 3088, 3318, 3319, 3320,
    3324, 3328, 3573, 3574, 3575, 3579, 3583, 3817, 3818, 3819]

theorem has_roots : ∀ k ∈ roots, ∃ e ∈ SL, e.1 = k := by
  have h : roots.all (CFSG.KC.Fi24Sev.hasU SL) = true := by decide +kernel
  exact fun k hk => CFSG.KS.Fi24SevB.hasU_spec (List.all_eq_true.1 h k hk)

theorem U_eq (hB : Bridge) {k : ℕ} (hk : k ∈ roots) : wordElt (CFSG.KD.Fi24KPerm.U k) = sK k := by
  obtain ⟨e, he, h1, h2⟩ := findU_spec (has_roots k hk)
  change wordElt (findU SL k) = _
  rw [h2, words_eq hB e he, h1]

theorem U_lt {k : ℕ} (hk : k ∈ roots) : ∀ l ∈ CFSG.KD.Fi24KPerm.U k, l < 26 := by
  obtain ⟨e, he, -, h2⟩ := findU_spec (has_roots k hk)
  change ∀ l ∈ findU SL k, l < 26
  rw [h2]
  exact sl_codes e he

theorem mW_eq (hB : Bridge) : ∀ (w : List ℕ), (∀ l ∈ w, l / 2 ∈ roots) →
    wordElt (mW SL w) =
      (w.map fun l => if l % 2 = 0 then sK (l / 2) else (sK (l / 2))⁻¹).prod ∧
      ∀ l ∈ mW SL w, l < 26
  | [], _ => ⟨rfl, nil_lt⟩
  | l :: w, hw => by
    obtain ⟨ih1, ih2⟩ := mW_eq hB w (fun l' h => hw l' (List.mem_cons_of_mem l h))
    have hk := hw l List.mem_cons_self
    change wordElt (lIf (Nat.beq (Nat.land l 1) 0) (findU SL (Nat.shiftRight l 1))
      (invC (findU SL (Nat.shiftRight l 1))) ++ mW SL w) = _ ∧ ∀ x ∈ lIf (Nat.beq (Nat.land l 1) 0)
      (findU SL (Nat.shiftRight l 1)) (invC (findU SL (Nat.shiftRight l 1))) ++ mW SL w, x < 26
    have hsh : Nat.shiftRight l 1 = l / 2 := by simp [Nat.shiftRight_eq_div_pow]
    have hland : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
    rw [hsh, hland, List.map_cons, List.prod_cons]
    by_cases hev : l % 2 = 0
    · rw [beq_of hev, lIf_true, ite_eq_left hev]
      change wordElt (CFSG.KD.Fi24KPerm.U (l / 2) ++ mW SL w) = _ ∧
        ∀ x ∈ CFSG.KD.Fi24KPerm.U (l / 2) ++ mW SL w, x < 26
      exact ⟨by rw [wordElt_append, ih1, U_eq hB hk], app_lt (U_lt hk) ih2⟩
    · rw [beq_ne hev, lIf_false, ite_eq_right hev]
      change wordElt (invC (CFSG.KD.Fi24KPerm.U (l / 2)) ++ mW SL w) = _ ∧
        ∀ x ∈ invC (CFSG.KD.Fi24KPerm.U (l / 2)) ++ mW SL w, x < 26
      refine ⟨?_, app_lt (CFSG.KD.Fi24ThreeO.invC_lt (U_lt hk)) ih2⟩
      rw [wordElt_append, ih1, wordElt_invC hB (U_lt hk), U_eq hB hk]

theorem heL_cons (x y : ℕ) (l : ℕ × Bool) (v : List (ℕ × Bool)) :
    CFSG.KD.Fi24KPerm.heL x y (l :: v) =
      (2 * (if l.1 = 0 then x else y) + (if l.2 then 0 else 1)) :: CFSG.KD.Fi24KPerm.heL x y v := by
  obtain ⟨i, e⟩ := l
  have hb : Nat.beq i 0 = decide (i = 0) := by cases i <;> rfl
  change List.cons (Nat.add (Nat.mul 2 (Bool.rec y x (Nat.beq i 0))) (Bool.rec 1 0 e)) _ = _
  rw [hb]
  by_cases hi : i = 0 <;> cases e <;> simp [hi] <;> rfl

theorem heL_prod (x y : ℕ) (v : List (ℕ × Bool)) :
    ((CFSG.KD.Fi24KPerm.heL x y v).map fun l =>
      if l % 2 = 0 then sK (l / 2) else (sK (l / 2))⁻¹).prod = wordProd (img2 (sK x) (sK y)) v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [heL_cons, List.map_cons, List.prod_cons, ih]
    unfold wordProd
    rw [List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, e⟩ := l
    have d0 : ∀ m : ℕ, 2 * m / 2 = m := fun m => by omega
    have d1 : ∀ m : ℕ, (2 * m + 1) / 2 = m := fun m => by omega
    have r0 : ∀ m : ℕ, 2 * m % 2 = 0 := fun m => by omega
    by_cases hi : i = 0 <;> cases e <;> simp [hi, img2, d0, d1, r0]

theorem heL_mem {x y : ℕ} (hx : x ∈ roots) (hy : y ∈ roots) (v : List (ℕ × Bool)) :
    ∀ l ∈ CFSG.KD.Fi24KPerm.heL x y v, l / 2 ∈ roots := by
  induction v with
  | nil => intro l hl; exact absurd hl List.not_mem_nil
  | cons a v ih =>
    intro l hl
    rw [heL_cons, List.mem_cons] at hl
    rcases hl with rfl | hl
    · obtain ⟨i, e⟩ := a
      have h2 : ∀ m n : ℕ, n ≤ 1 → (2 * m + n) / 2 = m := fun m n hn => by omega
      rw [h2 _ _ (by split <;> omega)]
      split
      · exact hx
      · exact hy
    · exact ih l hl

theorem fq_eq (hB : Bridge) {i : ℕ} (hi : i < 69) (hu : ∀ l ∈ (CFSG.KD.Fi24KPerm.fq i).1, l < 26)
    (hv : ∀ l ∈ (CFSG.KD.Fi24KPerm.fq i).2, l < 26) :
    wordElt (CFSG.KD.Fi24KPerm.fq i).1 = wordElt (CFSG.KD.Fi24KPerm.fq i).2 := by
  have hc := CFSG.KD.Fi24KPerm.Ck.fqcAll i hi
  have h : eqOK NW NT [CFSG.KD.Fi24KPerm.fq i] = true := by
    unfold eqOK
    refine allL_of fun p hp => ?_
    rw [List.mem_singleton] at hp
    rw [hp]
    exact hc
  exact eq_of_eqOK hB h List.mem_cons_self hu hv

theorem fqL_eq : CFSG.KD.Fi24KPerm.fqL = (List.range 69).map CFSG.KD.Fi24KPerm.fq := by
  decide +kernel

theorem fqL_codes : ∀ p ∈ CFSG.KD.Fi24KPerm.fqL, (∀ l ∈ p.1, l < 26) ∧ ∀ l ∈ p.2, l < 26 := by
  decide +kernel

theorem fqL_spec (hB : Bridge) {u v : List ℕ} (h : (u, v) ∈ CFSG.KD.Fi24KPerm.fqL) :
    wordElt u = wordElt v := by
  have hc := fqL_codes _ h
  rw [fqL_eq, List.mem_map] at h
  obtain ⟨i, hi, he⟩ := h
  have := fq_eq hB (List.mem_range.1 hi) (by rw [he]; exact hc.1) (by rw [he]; exact hc.2)
  rwa [he] at this

theorem rec_pure (L : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    List.rec (motive := fun _ => List (List ℕ × List ℕ)) List.nil
      (fun p _ ih => CFSG.KD.Fi24KPerm.pureL p ++ ih) L = L.flatMap CFSG.KD.Fi24KPerm.pureL := by
  induction L with
  | nil => rfl
  | cons p L ih => rw [List.flatMap_cons, ← ih]

theorem rec_rels (x y : ℕ) (R : List (List (ℕ × Bool))) :
    List.rec (motive := fun _ => List (List ℕ × List ℕ)) List.nil
      (fun v _ ih => (mW SL (CFSG.KD.Fi24KPerm.heL x y v), List.nil) :: ih) R =
      R.map fun v => (mW SL (CFSG.KD.Fi24KPerm.heL x y v), []) := by
  induction R with
  | nil => rfl
  | cons v R ih => rw [List.map_cons, ← ih]

theorem pure_mem {p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hp : p ∈ CFSG.KD.Fi24KPerm.pureT)
    {e : List ℕ × List ℕ} (he : e ∈ CFSG.KD.Fi24KPerm.pureL p) : e ∈ CFSG.KD.Fi24KPerm.fqL := by
  unfold CFSG.KD.Fi24KPerm.fqL
  rw [rec_pure]
  iterate 9 refine List.mem_cons_of_mem _ ?_
  exact List.mem_flatMap.2 ⟨p, hp, he⟩

theorem root_mem : ∀ p ∈ CFSG.KD.Fi24KPerm.pureT, p.2.1 ∈ roots ∧ p.2.2.1 ∈ roots ∧
    p.2.2.2.1 ∈ roots ∧ p.2.2.2.2.1 ∈ roots ∧ p.2.2.2.2.2 ∈ roots := by decide

theorem pure_of (hB : Bridge) {p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hp : p ∈ CFSG.KD.Fi24KPerm.pureT) :
    (∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      wordProd (img2 (sK p.2.1) (sK p.2.2.1)) v = 1) ∧ sK p.2.2.2.1 = sK 64 ∧
    sK p.2.2.2.2.1 = sK 66 ∧ sK p.2.2.2.2.2 * (sK 64 * sK 66 ^ p.1) = sK 67 * sK p.2.2.2.2.2 := by
  obtain ⟨rx, ry, rX, rY, rh⟩ := root_mem p hp
  have m : ∀ e ∈ CFSG.KD.Fi24KPerm.pureL p, wordElt e.1 = wordElt e.2 :=
    fun e he => fqL_spec hB (pure_mem hp he)
  unfold CFSG.KD.Fi24KPerm.pureL at m
  rw [rec_rels] at m
  have eX := m _ List.mem_cons_self
  have eY := m _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have eH := m _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  dsimp only at eX eY eH
  rw [U_eq hB rX, U_eq hB (k := 64) (by decide)] at eX
  rw [U_eq hB rY, U_eq hB (k := 66) (by decide)] at eY
  rw [wordElt_append, wordElt_append, wordElt_append, wordElt_pw, U_eq hB rh,
    U_eq hB (k := 64) (by decide), U_eq hB (k := 66) (by decide),
    U_eq hB (k := 67) (by decide)] at eH
  refine ⟨?_, eX, eY, eH⟩
  rw [CFSG.KD.OrdHe.rels_eq]
  intro v hv
  have e := m _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_map.2 ⟨v, hv, rfl⟩))))
  dsimp only at e
  rw [(mW_eq hB _ (heL_mem rx ry v)).1, heL_prod, wordElt_nil] at e
  exact e

theorem pureT_of {q : PureSec} (hq : q ∈ pureSecs) :
    (q.lam, q.ix, q.iy, q.oX, q.oY, q.oh) ∈ CFSG.KD.Fi24KPerm.pureT := by
  simp only [pureSecs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ne_ix (hB : Bridge) {q : PureSec} (hq : q ∈ pureSecs) : sK q.ix ≠ 1 := by
  have hn := CFSG.KD.Fi24KPerm.Ck.fNe_t
  unfold CFSG.KD.Fi24KPerm.fNe at hn
  have hx : q.ix ∈ roots := (root_mem _ (pureT_of hq)).1
  have hm : (CFSG.KD.Fi24KPerm.U q.ix, ([] : List ℕ)) ∈
      [(CFSG.KD.Fi24KPerm.U 2211, []), (CFSG.KD.Fi24KPerm.U 2546, []),
        (CFSG.KD.Fi24KPerm.U 2812, []), (CFSG.KD.Fi24KPerm.U 3084, []),
        (CFSG.KD.Fi24KPerm.U 3324, []), (CFSG.KD.Fi24KPerm.U 3579, [])] := by
    simp only [pureSecs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have n := ne_of_neOK hB hn hm (U_lt hx) nil_lt
  rwa [U_eq hB hx, wordElt_nil] at n

theorem comm_of (hB : Bridge) {i k : ℕ} (hi : i ∈ roots) (hk : k ∈ roots)
    (hp : (CFSG.KD.Fi24KPerm.U i ++ CFSG.KD.Fi24KPerm.U k,
      CFSG.KD.Fi24KPerm.U k ++ CFSG.KD.Fi24KPerm.U i) ∈ CFSG.KD.Fi24KPerm.fqL) :
    sK i * sK k = sK k * sK i := by
  have e := fqL_spec hB hp
  rwa [wordElt_append, wordElt_append, U_eq hB hi, U_eq hB hk] at e

theorem eq_of (hB : Bridge) {i k : ℕ} (hi : i ∈ roots) (hk : k ∈ roots)
    (hp : (CFSG.KD.Fi24KPerm.U i, CFSG.KD.Fi24KPerm.U k) ∈ CFSG.KD.Fi24KPerm.fqL) :
    sK i = sK k := by
  have e := fqL_spec hB hp
  rwa [U_eq hB hi, U_eq hB hk] at e

theorem mixed_eq (hB : Bridge) : ∀ m ∈ mixedSecs, sK m.ia = sK 0 ∧ sK m.ib = sK 1 := by
  intro m hm
  simp only [mixedSecs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨eq_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp),
      eq_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)⟩
  · exact ⟨eq_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp),
      eq_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)⟩

theorem secOK_WK {gs : List ℕ} {lo hi : ℕ} (h : secC (WE) gs lo hi = true) :
    secOK WK gs lo hi = true := by
  rw [WK_eq]
  exact CertificateChecks.KernelF24S.secOK_of_secC h

theorem mixed_sec : ∀ m ∈ mixedSecs, secOK WK m.gs m.lo m.hi = true ∧ m.lo ≤ m.ia ∧
    m.ia < m.hi ∧ m.lo ≤ m.ib ∧ m.ib < m.hi := by
  intro m hm
  have hd := CFSG.KC.SlpM.allL_spec CFSG.KD.F24S.mixedDataC_ok m hm
  unfold CFSG.KD.F24S.mixedDataC at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hd
  obtain ⟨hs0, h1, h2, h3, h4, -⟩ := hd
  exact ⟨secOK_WK hs0, h1, h2, h3, h4⟩

theorem pure_sec : ∀ q ∈ pureSecs, secOK WK (pureGens q.lam) q.lo q.hi = true ∧
    secOK WK [q.ix, q.iy] q.hi q.hi2 = true ∧ q.lo ≤ q.ix ∧ q.ix < q.hi ∧ q.lo ≤ q.iy ∧
    q.iy < q.hi ∧ q.hi ≤ q.oX ∧ q.oX < q.hi2 ∧ q.hi ≤ q.oY ∧ q.oY < q.hi2 ∧ q.hi ≤ q.oh ∧
    q.oh < q.hi2 := by
  intro q hq
  have hd := CFSG.KC.SlpM.allL_spec CFSG.KD.F24S.pureDataC_ok q hq
  unfold CFSG.KD.F24S.pureDataC at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hd
  obtain ⟨hc1, hc2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -⟩ := hd
  exact ⟨secOK_WK hc1, secOK_WK hc2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩

theorem fi24kGroup (hB : Bridge) : Fi24KGroup where
  size_words := by
    rw [CertificateChecks.KernelF24S.words_eq]
    simp [CertificateChecks.KernelF24S.w7_len]
  size_extra := by
    rw [CertificateChecks.KernelF24S.extraK_eq]
    simp [CertificateChecks.KernelF24S.ek_len]
  w0 := by
    rw [CertificateChecks.KernelF24S.words_eq]
    decide +kernel
  w1 := by
    rw [CertificateChecks.KernelF24S.words_eq]
    decide +kernel
  header := by
    rw [CertificateChecks.KernelF24S.extraK_eq]
    exact CertificateChecks.KernelF24S.header_ok
  mixedSec := mixed_sec
  pureSec := pure_sec
  comm85 := comm_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)
  comm86 := comm_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)
  comm82 := comm_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)
  comm83 := comm_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)
  comm84 := comm_of hB (by decide) (by decide) (by unfold CFSG.KD.Fi24KPerm.fqL; simp)
  mixedEq := mixed_eq hB
  pureEq := fun q hq => by
    obtain ⟨h1, h2, h3, h4⟩ := pure_of hB (pureT_of hq)
    exact ⟨h1, ne_ix hB hq, h2, h3, h4⟩

end CFSG.KD.Fi24KPerm.Final

end
