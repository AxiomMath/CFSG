module

public import Certificates.Kernel.SporSch.Ru.B1E8s0
public import Certificates.Kernel.SporSch.Ru.B1E8s1
public import Certificates.Kernel.SporSch.Ru.B1E8s2
public import Certificates.Kernel.SporSch.Ru.B1E8s3
public import Certificates.Kernel.SporSch.Ru.B1E8s4
public import Certificates.Kernel.SporSch.Ru.B1E8s5
public import Certificates.Kernel.SporSch.Ru.B1E8s6
public import Certificates.Kernel.SporSch.Ru.B1E8s7
public import Certificates.Kernel.SporSch.Ru.B1SCs0
public import Certificates.Kernel.SporSch.Ru.B1SCs1
public import Certificates.Kernel.SporSch.Ru.B1SCs2
public import Certificates.Kernel.SporSch.Ru.B1SCs3
public import Certificates.Kernel.SporSch.Ru.B1SCs4
public import Certificates.Kernel.SporSch.Ru.B1SCs5
public import Certificates.Kernel.SporSch.Ru.B1SCs6
public import Certificates.Kernel.SporSch.Ru.B1SCs7
public import Certificates.Kernel.SporSch.Ru.B1PR
public import Certificates.Kernel.SporSch.Ru.Rows2
public import CFSG.Certificates.Kernel.SporSch.RuDistIdx
public import Certificates.Data.GMS78RuB1Check
public import Certificates.Data.GMS78RuB1SCCheck
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.Rows2

theorem cWS : allN 24 (fun i => canonK 4060 12 (mask 12) (4060 * 12) (WS i)) = true := by quickRfl
theorem cWSI : allN 24 (fun i => canonK 4060 12 (mask 12) (4060 * 12) (WSI i)) = true := by
  quickRfl
theorem cSL : allN 12 (fun k => canonK 4060 12 (mask 12) (4060 * 12) (SL k)) = true := by quickRfl
theorem cSLI : allN 12 (fun k => canonK 4060 12 (mask 12) (4060 * 12) (SLI k)) = true := by
  quickRfl
theorem cBig : allN 15 (fun k => canonK 4060 12 (mask 12) (4060 * 12) (bigP k)) = true := by
  quickRfl
theorem cnt0' : Nat.beq (rcnt (RuS4.LR 0)) 2048 = true := by quickRfl

theorem lt_pow_of_shift {p N : Nat} (e : Nat.shiftRight p N = 0) : p < 2 ^ N := by
  have e' : p / 2 ^ N = 0 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact e
  exact (Nat.div_eq_zero_iff.1 e').resolve_left (Nat.two_pow_pos _).ne'

theorem lt_pow_of_canon {p : Nat} (h : canonK 4060 12 (mask 12) (4060 * 12) p = true) :
    p < 2 ^ (4060 * 12) := by
  unfold canonK at h
  have h2 := ((bAnd_iff (szOK 4060 12) _).1 h).2
  have h1 : Nat.beq (Nat.shiftRight p (4060 * 12)) 0 = true :=
    ((bAnd_iff (Nat.beq (Nat.shiftRight p (4060 * 12)) 0) _).1 h2).1
  exact lt_pow_of_shift (Nat.eq_of_beq_eq_true h1)

theorem list_eq_range {α : Type} (l : List α) (d : α) :
    l = (List.range l.length).map fun i => l.getD i d := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem allLt_eq_allN' {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allLt n f = allN n g := by
  cases ha : allLt n f <;> cases hg : allN n g
  · rfl
  · exact absurd (allLt_iff.2 fun i hi => (h i hi) ▸ allN_spec hg i hi) (by rw [ha]; decide)
  · exact absurd (CFSG.KS.Raw.allN_of_forall fun i hi => (h i hi) ▸ allLt_iff.1 ha i hi)
      (by rw [hg]; decide)
  · rfl

theorem beq_key {N a b c d : Nat} (hb : b < 2 ^ N) (hd : d < 2 ^ N) :
    Nat.beq (Nat.add (Nat.mul a (Nat.pow 2 N)) b) (Nat.add (Nat.mul c (Nat.pow 2 N)) d) =
      (Nat.beq a c && Nat.beq b d) := beq_pair hb hd

theorem le_of_ble' {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem not_true_or' (b : Bool) : (!true || b) = b := by cases b <;> rfl

theorem cG {G X : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true)
    (hX : canonK 4060 12 (mask 12) (4060 * 12) X = true) :
    canonK 4060 12 (mask 12) (4060 * 12) (pc G X) = true := canonK_pcomp hG hX

theorem cu {G X : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true)
    (hX : canonK 4060 12 (mask 12) (4060 * 12) X = true) :
    compA 4060 (unpack 4060 12 G) (unpack 4060 12 X) = unpack 4060 12 (pc G X) :=
  compA_unpack hG hX

@[expose] noncomputable def dq : List Int × Array Nat × Array Nat := ([], #[], #[])

theorem e8W_len : e8W.length = 24 := by simp [e8W, e8ConjWords]

theorem sginv : ruSGensA.map ruInv = rawInvs 4060 ruSGensA := by simp [rawInvs, ruInv]

theorem wok_spec {i : Nat} (hi : i < 24) :
    wordA 4060 ruSGensA (rawInvs 4060 ruSGensA) (e8ConjWords.getD i []) = unpack 4060 12 (WS i) ∧
      lettersOK 4 (e8ConjWords.getD i []) = true ∧
      permOK 4060 12 (mask 12) (4060 * 12) (WS i) (WSI i) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec wsOK i hi)
  have h := wordEqK_sound RuCe.sgBinds pSG h1
  rw [dword_zero] at h
  exact ⟨h.1, h.2, h2⟩

theorem e8W_get {i : Nat} (hi : i < 24) :
    e8W.getD i dq = (e8ConjWords.getD i [], unpack 4060 12 (WS i), unpack 4060 12 (WSI i)) := by
  obtain ⟨h1, -, h3⟩ := wok_spec hi
  have hl : i < e8ConjWords.length := by
    have e : e8ConjWords.length = 24 := rfl
    rw [e]
    exact hi
  have e : e8W.getD i dq = (e8ConjWords.getD i [],
      wordA 4060 ruSGensA (ruSGensA.map ruInv) (e8ConjWords.getD i []),
      invCand 4060 (wordA 4060 ruSGensA (ruSGensA.map ruInv) (e8ConjWords.getD i []))) := by
    unfold e8W
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  rw [e, sginv, h1, (invEqK_sound h3).1]

theorem conjBy_eq {i G : Nat} (hi : i < 24) (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true) :
    conjBy (e8W.getD i dq) (unpack 4060 12 G) = unpack 4060 12 (wconj i G) := by
  rw [e8W_get hi, conjBy]
  dsimp only
  rw [cu (allN_spec cWS i hi) hG, cu (cG (allN_spec cWS i hi) hG)
    (allN_spec cWSI i hi)]
  rfl

theorem cW {i G : Nat} (hi : i < 24) (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true) :
    canonK 4060 12 (mask 12) (4060 * 12) (wconj i G) = true :=
  cG (cG (allN_spec cWS i hi) hG) (allN_spec cWSI i hi)

theorem bigIdx {i : Nat} (hi : i < 8) : e8BigIdx.getD i 0 < 35 := by
  interval_cases i <;> simp [e8BigIdx]

theorem bigElt_eq {k : Nat} (hk : k < 15) : bigElt ruEArr xList k = unpack 4060 12 (bigP k) := by
  rw [bigElt, bigP]
  by_cases h : k < 7
  · have e : Nat.blt k 7 = true := Nat.blt_eq.mpr h
    rw [ite_eq_left h, e]
    exact e_eq h
  · have e : Nat.blt k 7 = false := by
      cases e' : Nat.blt k 7
      · rfl
      · exact absurd (Nat.blt_eq.mp e') h
    rw [ite_eq_right h, e]
    exact xl_eq (bigIdx (by omega))

theorem invP_eq {G : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true) :
    invP G = ruIsInvolA (unpack 4060 12 G) := by
  rw [invP, ruIsInvolA, cu hG hG, idA_eq, eqA_canon (cG hG hG) cId, eqA_canon hG cId]
  cases Nat.beq G (pidn 4060 12) <;> rfl

theorem g2_eq {T0 T1 x : Nat} (hx : x < 4060) :
    pg 12 (mask 12) (pcomp 4060 12 (mask 12) T0 T1) x = g2 T0 T1 x :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem sqFix_of_sq {T0 T1 x : Nat} (hx : x < 4060)
    (h : Nat.beq (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) T0 T1)
      (pcomp 4060 12 (mask 12) T0 T1)) (pidn 4060 12) = true) : sqFix T0 T1 x = true := by
  have e := Nat.eq_of_beq_eq_true h
  have e2 : pg 12 (mask 12) (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) T0 T1)
      (pcomp 4060 12 (mask 12) T0 T1)) x = pg 12 (mask 12) (pidn 4060 12) x := by
    rw [e]
  rw [CFSG.KS.PF.pg_pcomp (by norm_num) hx, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hx,
    g2_eq hx] at e2
  unfold sqFix
  rw [CFSG.KS.PackFld.strictB_eqP]
  cases hy : Nat.blt (g2 T0 T1 x) 4060
  · rfl
  · have hy' : g2 T0 T1 x < 4060 := Nat.blt_eq.mp hy
    rw [g2_eq hy'] at e2
    change Nat.beq (g2 T0 T1 (g2 T0 T1 x)) x = true
    rw [e2]
    exact Nat.beq_refl x

theorem sqFix_of_inv {T0 T1 x : Nat} (hx : x < 4060)
    (h : invP (pcomp 4060 12 (mask 12) T0 T1) = true) : sqFix T0 T1 x = true := by
  unfold invP at h
  exact sqFix_of_sq hx ((bAnd_iff _ _).1 h).1

theorem sqAll_of_sq {T0 T1 : Nat}
    (h : Nat.beq (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) T0 T1)
      (pcomp 4060 12 (mask 12) T0 T1)) (pidn 4060 12) = true) :
    ∀ l : List Nat, (∀ x ∈ l, x < 4060) → sqAll T0 T1 l = true
  | [], _ => rfl
  | x :: l, hl => by
    change bAnd(sqFix T0 T1 x, sqAll T0 T1 l) = true
    rw [sqFix_of_sq (hl x List.mem_cons_self) h,
      sqAll_of_sq h l fun y hy => hl y (List.mem_cons_of_mem _ hy)]

theorem sqAll_of_inv {T0 T1 : Nat} (h : invP (pcomp 4060 12 (mask 12) T0 T1) = true) :
    ∀ l : List Nat, (∀ x ∈ l, x < 4060) → sqAll T0 T1 l = true := by
  unfold invP at h
  exact sqAll_of_sq ((bAnd_iff _ _).1 h).1

noncomputable def keyF (H : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.lor (Nat.shiftLeft ih 12) (pg 12 (mask 12) H x)) l

theorem keyC_eq {T0 T1 i : Nat} (hi : i < 24) :
    ∀ l : List Nat, (∀ x ∈ l, x < 4060) →
      keyC T0 T1 i l = keyF (wconj i (pcomp 4060 12 (mask 12) T0 T1)) l
  | [], _ => rfl
  | x :: l, hl => by
    have hx := hl x List.mem_cons_self
    have hr := allN_spec (range_of_canonK (allN_spec cWSI i hi)) x hx
    have hw : pg 12 (mask 12) (WSI i) x < 4060 := Nat.blt_eq.mp hr
    change Nat.lor (Nat.shiftLeft (keyC T0 T1 i l) 12)
        (pg 12 (mask 12) (WS i) (g2 T0 T1 (pg 12 (mask 12) (WSI i) x))) =
      Nat.lor (Nat.shiftLeft (keyF (wconj i (pcomp 4060 12 (mask 12) T0 T1)) l) 12)
        (pg 12 (mask 12) (wconj i (pcomp 4060 12 (mask 12) T0 T1)) x)
    rw [keyC_eq hi l fun y hy => hl y (List.mem_cons_of_mem _ hy), wconj,
      CFSG.KS.PF.pg_pcomp (by norm_num) hx, CFSG.KS.PF.pg_pcomp (by norm_num) hw, g2_eq hw]

theorem distNL_eq_card : ∀ l : List Nat, distNL l = l.toFinset.card
  | [] => rfl
  | x :: l => by
    rw [distNL_cons, List.toFinset_cons, distNL_eq_card l]
    by_cases h : x ∈ l
    · rw [ite_eq_left h, Finset.card_insert_of_mem (List.mem_toFinset.2 h)]
    · rw [ite_eq_right h, Finset.card_insert_of_notMem (fun h' => h (List.mem_toFinset.1 h'))]

theorem distNL_map_le (f : Nat → Nat) (l : List Nat) : distNL (l.map f) ≤ distNL l := by
  have e : (l.map f).toFinset = l.toFinset.image f := by
    ext y
    simp
  rw [distNL_eq_card, distNL_eq_card, e]
  exact Finset.card_image_le

theorem keyPts_lt : ∀ x ∈ keyPts, x < 4060 := by
  unfold keyPts
  decide

theorem sqPts_lt : ∀ x ∈ sqPts, x < 4060 := by
  unfold sqPts
  decide

theorem dist_le (T0 T1 : Nat) :
    distNL ((List.range 24).map fun i => keyC T0 T1 i keyPts) ≤
      nConj (pcomp 4060 12 (mask 12) T0 T1) := by
  have e : ((List.range 24).map fun i => keyC T0 T1 i keyPts) =
      ((List.range 24).map fun i => wconj i (pcomp 4060 12 (mask 12) T0 T1)).map
        (fun H => keyF H keyPts) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    exact keyC_eq (List.mem_range.1 hi) keyPts keyPts_lt
  rw [e, nConj]
  exact distNL_map_le _ _

theorem e8pK_of_F {T0 T1 : Nat} (h : e8pF T0 T1 = true) :
    e8pK (pcomp 4060 12 (mask 12) T0 T1) = true := by
  unfold e8pF at h
  cases hs : sqAll T0 T1 sqPts
  · unfold e8pK
    cases hi : invP (pcomp 4060 12 (mask 12) T0 T1)
    · rfl
    · rw [sqAll_of_inv hi sqPts sqPts_lt] at hs
      exact absurd hs (by decide)
  · rw [hs] at h
    cases hd : Nat.ble 9 (distNL ((List.range 24).map fun i => keyC T0 T1 i keyPts))
    · rw [hd] at h
      exact h
    · unfold e8pK
      cases hi : invP (pcomp 4060 12 (mask 12) T0 T1)
      · rfl
      · change bIf(bigQ (pcomp 4060 12 (mask 12) T0 T1), true,
          Nat.ble 9 (nConj (pcomp 4060 12 (mask 12) T0 T1))) = true
        cases bigQ (pcomp 4060 12 (mask 12) T0 T1)
        · exact Nat.ble_eq.mpr (Nat.le_trans (Nat.le_of_ble_eq_true hd) (dist_le T0 T1))
        · rfl

theorem e8row_of_F {a : Nat} (h : e8rowF a = true) : e8row a = true := by
  unfold e8rowF at h
  unfold e8row row2K
  simp only [CFSG.KS.PackFld.strictB_eqP] at h ⊢
  exact CFSG.KS.PackFld.allN_of_forall fun b hb => e8pK_of_F (allN_spec h b hb)

theorem e8rows : ∀ a < rcnt (RuS4.LR 0), e8row a = true := by
  intro a ha
  rw [Nat.eq_of_beq_eq_true cnt0'] at ha
  refine e8row_of_F ?_
  have g : ∀ (o : Nat), (∀ b < 256, e8rowF (Nat.add o b) = true) → o ≤ a → a < o + 256 →
      e8rowF a = true := fun o h h1 h2 => by
    have e := h (a - o) (by omega)
    have e2 : Nat.add o (a - o) = a := Nat.add_sub_of_le h1
    rwa [e2] at e
  rcases (by omega : a < 256 ∨ (256 ≤ a ∧ a < 512) ∨ (512 ≤ a ∧ a < 768) ∨
    (768 ≤ a ∧ a < 1024) ∨ (1024 ≤ a ∧ a < 1280) ∨ (1280 ≤ a ∧ a < 1536) ∨
    (1536 ≤ a ∧ a < 1792) ∨ (1792 ≤ a ∧ a < 2048)) with h | h | h | h | h | h | h | h
  · exact E8S0.all a h
  · exact g 256 E8S1.all h.1 h.2
  · exact g 512 E8S2.all h.1 h.2
  · exact g 768 E8S3.all h.1 h.2
  · exact g 1024 E8S4.all h.1 h.2
  · exact g 1280 E8S5.all h.1 h.2
  · exact g 1536 E8S6.all h.1 h.2
  · exact g 1792 E8S7.all h.1 h.2

theorem e8inv : all2 4060 ruLevS (fun t => !ruIsInvolA t ||
    (Nat.any 15 fun k _ => eqA 4060 t (bigElt ruEArr xList k)) ||
    decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2 p'.2) (e8W.map fun q => (q, conjBy q t))).length)) =
    true := by
  refine all2_of_rows_imp bindsS4 RuS4M.perm RuS4.hl (Nat.le_refl 2) (fun G hG h => ?_) e8rows
  unfold e8pK at h
  rw [← invP_eq hG]
  cases hi : invP G
  · rfl
  · rw [hi] at h
    rw [not_true_or']
    cases hb : bigQ G
    · rw [hb] at h
      have h' : Nat.ble 9 (nConj G) = true := h
      have hl : (pickBy (fun p p' => eqA 4060 p.2 p'.2)
          (e8W.map fun q => (q, conjBy q (unpack 4060 12 G)))).length = nConj G := by
        rw [list_eq_range e8W dq, e8W_len, List.map_map]
        refine pickBy_length_idx (K := fun i => wconj i G) fun i hi j hj => ?_
        simp only [Function.comp_apply]
        rw [conjBy_eq hi hG, conjBy_eq hj hG, eqA_canon (cW hi hG) (cW hj hG)]
      rw [hl, decide_eq_true (le_of_ble' h'), Bool.or_true]
    · have hb' : anyK 15 (fun k => Nat.beq G (bigP k)) = true := hb
      obtain ⟨k, hk, e⟩ := anyK_spec hb'
      have hany : (Nat.any 15 fun k _ => eqA 4060 (unpack 4060 12 G) (bigElt ruEArr xList k)) =
          true := nat_any_of hk (by
            rw [bigElt_eq hk, ← Nat.eq_of_beq_eq_true e]
            exact eqK_sound (Nat.beq_refl G))
      rw [hany]
      rfl

theorem pairCond_eq {A B : Nat} (hA : canonK 4060 12 (mask 12) (4060 * 12) A = true)
    (hB : canonK 4060 12 (mask 12) (4060 * 12) B = true) :
    pairCond (unpack 4060 12 A) (unpack 4060 12 B) = pairCondK A B := by
  rw [pairCond, pairCondK, z_eq, eqA_canon hB RuF.zCanon, eqA_canon hB hA,
    cu RuF.zCanon hA, eqA_canon hB (cG RuF.zCanon hA), cu hA hB,
    cu hB hA, eqA_canon (cG hA hB) (cG hB hA)]

theorem pr_spec {k k' : Nat} (hk : k < 8) (hk' : k' < 15) :
    (!pairCondK (bigP (7 + k)) (bigP k') || Nat.ble 9 (distNL ((List.range 24).map fun i =>
      keyP i (bigP (7 + k)) (bigP k')))) = true := by
  have hj : 15 * k + k' < 120 := by omega
  have h := PRC.all (15 * k + k') hj
  unfold pairOK at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (15 * k + k') 15 = k := by
    change (15 * k + k') / 15 = k
    omega
  have e2 : Nat.mod (15 * k + k') 15 = k' := by
    change (15 * k + k') % 15 = k'
    omega
  rw [e1, e2] at h
  exact h

theorem e8pairs : (allLt 8 fun k => allLt 15 fun k' =>
    let a := bigElt ruEArr xList (7 + k)
    let b := bigElt ruEArr xList k'
    !pairCond a b || decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2.1 p'.2.1 &&
      eqA 4060 p.2.2 p'.2.2) (e8W.map fun q => (q, conjBy q a, conjBy q b))).length)) = true := by
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro k' hk'
  have cA := allN_spec cBig (7 + k) (by omega)
  have cB := allN_spec cBig k' (by omega)
  dsimp only
  rw [bigElt_eq (by omega), bigElt_eq hk', pairCond_eq cA cB]
  have h := pr_spec hk hk'
  cases hp : pairCondK (bigP (7 + k)) (bigP k')
  · rfl
  · rw [hp, not_true_or'] at h
    rw [not_true_or']
    have hl : (pickBy (fun p p' => eqA 4060 p.2.1 p'.2.1 && eqA 4060 p.2.2 p'.2.2)
        (e8W.map fun q => (q, conjBy q (unpack 4060 12 (bigP (7 + k))),
          conjBy q (unpack 4060 12 (bigP k'))))).length =
        distNL ((List.range 24).map fun i => keyP i (bigP (7 + k)) (bigP k')) := by
      rw [list_eq_range e8W dq, e8W_len, List.map_map]
      refine pickBy_length_idx (K := fun i => keyP i (bigP (7 + k)) (bigP k')) fun i hi j hj => ?_
      simp only [Function.comp_apply]
      rw [conjBy_eq hi cA, conjBy_eq hj cA, conjBy_eq hi cB, conjBy_eq hj cB,
        eqA_canon (cW hi cA) (cW hj cA), eqA_canon (cW hi cB) (cW hj cB), keyP, keyP]
      exact (beq_key (lt_pow_of_canon (cW hi cB)) (lt_pow_of_canon (cW hj cB))).symm
    rw [hl, decide_eq_true (le_of_ble' h)]

theorem e8Check : ruB1E8Check = true := by
  unfold ruB1E8Check e8CheckWith
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, e8inv⟩, e8pairs⟩
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi' : i < 24 := by simpa [e8ConjWords] using hi
    have := (wok_spec hi').2.1
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    have hi' : i < 24 := by rwa [e8W_len] at hi
    have e := e8W_get hi'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at e
    rw [e]
    exact (invEqK_sound (wok_spec hi').2.2).2

theorem scGensInv_eq : scGensInv = rawInvs 4060 scGens := by
  simp [scGensInv, scGens, rawInvs, ruInv]

theorem g4Binds : scGens.size = 4 ∧ ∀ j < 4, scGens[j]! = unpack 4060 12 (g4 j) :=
  ⟨rfl, fun j hj => by
    rcases j with _ | _ | _ | _ | j
    exacts [c0_eq, c1_eq, ns0_eq, ns1_eq, absurd hj (by omega)]⟩

theorem g4Perm : allN 4 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (g4 j) (g4i j)) = true :=
  CFSG.KS.Raw.allN_of_forall fun j hj => by
    rcases j with _ | _ | _ | _ | j
    exacts [pC0, pC1, pNs0, pNs1, absurd hj (by omega)]

theorem slok_spec {k : Nat} (hk : k < 12) :
    scL (scWords.getD k []) = unpack 4060 12 (SL k) ∧ lettersOK 4 (scWords.getD k []) = true ∧
      permOK 4060 12 (mask 12) (4060 * 12) (SL k) (SLI k) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (SLC.all k hk)
  have h := wordEqK_sound g4Binds g4Perm h1
  rw [dword_zero] at h
  exact ⟨by rw [scL, scGensInv_eq]; exact h.1, h.2, h2⟩

theorem se_eq {k i : Nat} (hk : k < 12) (hi : i < 7) :
    (scConjE (scWords.getD k []))[i]! = unpack 4060 12 (SE (7 * k + i)) := by
  obtain ⟨h1, -, h3⟩ := slok_spec hk
  have hj : 7 * k + i < 84 := by omega
  have hs := SEC.all (7 * k + i) hj
  unfold seok at hs
  have e1 : Nat.div (7 * k + i) 7 = k := by
    change (7 * k + i) / 7 = k
    omega
  have e2 : Nat.mod (7 * k + i) 7 = i := by
    change (7 * k + i) % 7 = i
    omega
  rw [e1, e2] at hs
  obtain ⟨hs1, -⟩ := (bAnd_iff _ _).1 hs
  have hsz : ruEArr.size = 7 := e_size
  rw [scConjE, getElem!_pos _ i (by simp [hsz]; omega), Array.getElem_map,
    ← getElem!_pos ruEArr i (by rw [hsz]; omega), ruConjA, h1, (invEqK_sound h3).1, e_eq hi,
    cu (allN_spec cSL k hk) (cEi' hi),
    cu (cG (allN_spec cSL k hk) (cEi' hi)) (allN_spec cSLI k hk),
    ← Nat.eq_of_beq_eq_true hs1]
where cEi' {i : Nat} (hi : i < 7) : canonK 4060 12 (mask 12) (4060 * 12) (EA i) = true :=
  allN_spec cE i hi

theorem cSE {j : Nat} (hj : j < 84) : canonK 4060 12 (mask 12) (4060 * 12) (SE j) = true :=
  ((bAnd_iff _ _).1 (SEC.all j hj)).2

theorem anyK_mono {n : Nat} {f g : Nat → Bool} (hfg : ∀ i, f i = true → g i = true)
    (h : anyK n f = true) : anyK n g = true := by
  unfold anyK at h ⊢
  cases hg : allN n (fun i => bIf(g i, false, true))
  · rfl
  · have hf : allN n (fun i => bIf(f i, false, true)) = true :=
      CFSG.KS.PackFld.allN_of_forall fun i hi => by
        have e : bIf(g i, false, true) = true := allN_spec hg i hi
        change bIf(f i, false, true) = true
        cases hfi : f i
        · rfl
        · rw [hfg i hfi] at e
          exact absurd e (by decide)
    rw [hf] at h
    exact absurd h (by decide)

theorem allN_mono' {n : Nat} {f g : Nat → Bool} (hfg : ∀ i, f i = true → g i = true)
    (h : allN n f = true) : allN n g = true :=
  CFSG.KS.PackFld.allN_of_forall fun i hi => hfg i (allN_spec h i hi)

theorem cm4_of_cmF {G X : Nat} (h : cmF G X = true) : cm4 G X = true :=
  ((bAnd_iff _ _).1 h).2

theorem scpK_of_G {G : Nat} (h : scpG G = true) : scpK G = true := by
  unfold scpG at h
  unfold scpK
  cases hq : Nat.beq (pc G G) (pidn 4060 12)
  · rfl
  · rw [hq] at h
    cases hc : allN 7 (fun j => cmF G (EA j))
    · rw [hc] at h
      have h' : anyK 12 (fun k => allN 7 (fun i => cmF G (SE (Nat.add (Nat.mul 7 k) i)))) = true :=
        h
      have h2 := anyK_mono (fun k => allN_mono' fun i => cm4_of_cmF) h'
      cases allN 7 (fun j => cm4 G (EA j))
      · exact h2
      · rfl
    · have e := allN_mono' (g := fun j => cm4 G (EA j)) (fun j => cm4_of_cmF) hc
      cases hc2 : allN 7 (fun j => cm4 G (EA j))
      · rw [hc2] at e
        exact absurd e (by decide)
      · rfl

theorem scpK_of_F {T0 T1 : Nat} (h : scpF T0 T1 = true) :
    scpK (pcomp 4060 12 (mask 12) T0 T1) = true := by
  unfold scpF at h
  cases hs : sqAll T0 T1 sqPts
  · unfold scpK
    cases hq : Nat.beq (pc (pcomp 4060 12 (mask 12) T0 T1) (pcomp 4060 12 (mask 12) T0 T1))
      (pidn 4060 12)
    · rfl
    · rw [sqAll_of_sq hq sqPts sqPts_lt] at hs
      exact absurd hs (by decide)
  · rw [hs, CFSG.KS.PackFld.strictB_eqP] at h
    exact scpK_of_G h

theorem scrow_of_F {a : Nat} (h : scrowF a = true) : scrow a = true := by
  unfold scrowF at h
  unfold scrow row2K
  simp only [CFSG.KS.PackFld.strictB_eqP] at h ⊢
  exact CFSG.KS.PackFld.allN_of_forall fun b hb => scpK_of_F (allN_spec h b hb)

theorem scrows : ∀ a < rcnt (RuS4.LR 0), scrow a = true := by
  intro a ha
  rw [Nat.eq_of_beq_eq_true cnt0'] at ha
  refine scrow_of_F ?_
  have g : ∀ (o : Nat), (∀ b < 256, scrowF (Nat.add o b) = true) → o ≤ a → a < o + 256 →
      scrowF a = true := fun o h h1 h2 => by
    have e := h (a - o) (by omega)
    have e2 : Nat.add o (a - o) = a := Nat.add_sub_of_le h1
    rwa [e2] at e
  rcases (by omega : a < 256 ∨ (256 ≤ a ∧ a < 512) ∨ (512 ≤ a ∧ a < 768) ∨
    (768 ≤ a ∧ a < 1024) ∨ (1024 ≤ a ∧ a < 1280) ∨ (1280 ≤ a ∧ a < 1536) ∨
    (1536 ≤ a ∧ a < 1792) ∨ (1792 ≤ a ∧ a < 2048)) with h | h | h | h | h | h | h | h
  · exact SCS0.all a h
  · exact g 256 SCS1.all h.1 h.2
  · exact g 512 SCS2.all h.1 h.2
  · exact g 768 SCS3.all h.1 h.2
  · exact g 1024 SCS4.all h.1 h.2
  · exact g 1280 SCS5.all h.1 h.2
  · exact g 1536 SCS6.all h.1 h.2
  · exact g 1792 SCS7.all h.1 h.2

theorem scComm_eq {G X : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true)
    (hX : canonK 4060 12 (mask 12) (4060 * 12) X = true) :
    scComm (unpack 4060 12 G) (unpack 4060 12 X) = cm4 G X := by
  rw [scComm, cu hG hX, cu hX hG, eqA_canon (cG hG hX) (cG hX hG)]
  rfl

theorem scAll2 : all2 4060 ruLevS scTest = true := by
  refine all2_of_rows_imp bindsS4 RuS4M.perm RuS4.hl (Nat.le_refl 2) (fun G hG h => ?_) scrows
  unfold scpK at h
  unfold scTest
  rw [cu hG hG, idA_eq, eqA_canon (cG hG hG) cId]
  cases hs : Nat.beq (pc G G) (pidn 4060 12)
  · rfl
  · rw [hs] at h
    rw [not_true_or']
    have hsz : ruEArr.size = 7 := e_size
    have hE : (allLt 7 fun j => scComm (unpack 4060 12 G) ruEArr[j]!) =
        allN 7 (fun j => cm4 G (EA j)) :=
      allLt_eq_allN' fun j hj => by rw [e_eq hj]; exact scComm_eq hG (allN_spec cE j hj)
    rw [hE]
    cases hc : allN 7 (fun j => cm4 G (EA j))
    · rw [hc] at h
      have h' : anyK 12 (fun k => allN 7 (fun i => cm4 G (SE (Nat.add (Nat.mul 7 k) i)))) = true := h
      obtain ⟨k, hk, hk'⟩ := anyK_spec h'
      rw [Bool.false_or, List.any_eq_true]
      refine ⟨scConjE (scWords.getD k []), ?_, ?_⟩
      · rw [scEs]
        have hk2 : k < scWords.length := by simp [scWords]; omega
        refine List.mem_map.2 ⟨_, ?_, rfl⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some]
        exact List.getElem_mem hk2
      · rw [allLt_eq_allN' (g := fun i => cm4 G (SE (Nat.add (Nat.mul 7 k) i))) fun i hi => by
          rw [se_eq hk hi]; exact scComm_eq hG (cSE (by omega))]
        exact hk'
    · rfl

theorem scCheck : ruB1SCCheck = true := by
  unfold ruB1SCCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by rw [e_size]; rfl, ?_⟩, ?_⟩, ?_⟩, scAll2⟩
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < 12 := by simpa [scWords] using hk
    have := (slok_spec hk').2.1
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < 12 := by simpa [scWords] using hk
    obtain ⟨h1, -, h3⟩ := slok_spec hk'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at h1
    rw [ruInv, h1, (invEqK_sound h3).1]
    exact (invEqK_sound h3).2
  · rw [List.all_eq_true]
    intro E hE
    rw [scEs] at hE
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hE
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < 12 := by simpa [scWords] using hk
    rw [allLt_iff]
    intro i hi
    have e := se_eq hk' hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at e
    rw [e]
    have hj : 7 * k + i < 84 := by omega
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (SES.all (7 * k + i) hj)
    exact siftK_sound bindsS4 RuS4M.perm RuS4.hl rfl (range_of_canonK (cSE hj)) h2

open Certificates in
open CFSG in
theorem facts : CFSG.Sporadic.RuSchreier.RuB1.ruB1E8Check = true ∧
    CFSG.Sporadic.RuSchreier.RuB1.ruB1XCheck = true ∧
    CFSG.Sporadic.RuSchreier.RuB1.ruB1SCCheck = true := ⟨e8Check, xCheck, scCheck⟩

end CertificateChecks.KernelSporSch.RuB1K

end
