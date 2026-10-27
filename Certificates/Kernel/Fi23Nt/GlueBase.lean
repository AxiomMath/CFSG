module

public import Certificates.Kernel.Fi23Nt.Sound
public import Certificates.Kernel.Fi23Nt.PosChkDefs
public import Certificates.Data.Kernel.Fi23Nt.DDDefs

@[expose] public section

namespace CertificateChecks.KernelFi23Nt

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Nt
  CFSG.KC.Fi23R CertificateChecks.KernelFi23Q CFSG.KS.Fi23Nt CFSG.KS.E27Lie
  CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist CFSG.KD.Fi23Nt
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CFSG.Perm
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

theorem wokK_spec : ∀ {w : List ℕ}, wokK w = true → ∀ r ∈ w, 52 ≤ r ∧ r < 76
  | [], _, _, hr => absurd hr List.not_mem_nil
  | r :: w, h, s, hs => by
    change Bool.rec (motive := fun _ => Bool) false (wokK w)
      (Bool.rec (motive := fun _ => Bool) false (Nat.blt r 76) (Nat.ble 52 r)) = true at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨Eq.mp Nat.ble_eq h3, Eq.mp Nat.blt_eq h4⟩
    · exact wokK_spec h2 s hs

theorem wsokK_spec : ∀ {W : List (List ℕ)}, wsokK W = true → ∀ w ∈ W, wokK w = true
  | [], _, _, hw => absurd hw List.not_mem_nil
  | w :: Ws, h, v, hv => by
    change Bool.rec (motive := fun _ => Bool) false (wsokK Ws) (wokK w) = true at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hv with rfl | hv
    · exact h1
    · exact wsokK_spec h2 v hv

theorem wok_of {w : List ℕ} (h : wokK w = true) : WOK w := fun r hr => Or.inr (wokK_spec h r hr)

theorem woks_of {W : List (List ℕ)} (h : wsokK W = true) : ∀ w ∈ W, WOK w :=
  fun w hw => wok_of (wsokK_spec h w hw)

theorem getD_mem_of {P : List ℕ → Prop} (W : List (List ℕ)) (hW : ∀ w ∈ W, P w) (h0 : P [])
    (j : ℕ) : P (W.getD j []) := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[j]? with _ | w
  · exact h0
  · exact hW w (List.mem_iff_getElem?.2 ⟨j, h⟩)

theorem forall2_mem {α β : Type} {R : α → β → Prop} :
    ∀ {I : List α} {Ws : List β}, List.Forall₂ R I Ws → ∀ w ∈ Ws, ∃ i ∈ I, R i w
  | _, _, List.Forall₂.nil => fun _ hw => absurd hw List.not_mem_nil
  | _, _, List.Forall₂.cons (a := a0) h t => fun w hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨a0, List.mem_cons_self, h⟩
    · obtain ⟨i, hi, hr⟩ := forall2_mem t w hw
      exact ⟨i, List.mem_cons_of_mem _ hi, hr⟩

theorem forall2_getD {R : ℕ → List ℕ → Prop} :
    ∀ {I : List ℕ} {Ws : List (List ℕ)}, List.Forall₂ R I Ws → ∀ t < I.length,
      R (I.getD t 0) (Ws.getD t []) ∧ Ws.getD t [] ∈ Ws
  | _, _, List.Forall₂.nil => fun _ ht => absurd ht (Nat.not_lt_zero _)
  | _, _, List.Forall₂.cons h r => fun t ht => by
    cases t with
    | zero => exact ⟨h, List.mem_cons_self⟩
    | succ t =>
      obtain ⟨h1, h2⟩ := forall2_getD r t (by simpa using ht)
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem fstK_eq : ∀ S : List (List ℕ × Bool), fstK S = S.map Prod.fst
  | [] => rfl
  | s :: S => by
    change s.1 :: fstK S = _
    rw [fstK_eq S, List.map_cons]


theorem wE_append (u v : List ℕ) : wE (u ++ v) = wE u * wE v := by
  simp only [wE, List.map_append, List.prod_append]


theorem pairG_mul {j : ℕ} (hj : j < 12) : pairG gs (2 * j + 1) * pairG gs (2 * j) = 1 := by
  refine eq_of_base fun t ht => ?_
  have ht' : t < 31671 := by omega
  rw [idx_mul, idx_one, letter_acts (l := 2 * j) (by omega) t ht',
    letter_acts (l := 2 * j + 1) (by omega) (tb G (52 + 2 * j) t) (LL_lt (l := 2 * j) (by omega) ht')]
  exact letter_inv hj ht'

theorem xor_tab : ∀ j < 12, Nat.xor (2 * j) 1 = 2 * j + 1 ∧ Nat.xor (2 * j + 1) 1 = 2 * j := by
  decide +kernel

theorem pairG_xor {l : ℕ} (hl : l < 24) : pairG gs (Nat.xor l 1) = (pairG gs l)⁻¹ := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · rw [(xor_tab j (by omega)).1]
    exact eq_inv_of_mul_eq_one_left (pairG_mul (by omega))
  · rw [(xor_tab j (by omega)).2]
    exact eq_inv_of_mul_eq_one_right (pairG_mul (by omega))

theorem reg_tab : ∀ r < 76, 52 ≤ r → ¬ Nat.xor r 1 < 10 ∧ Nat.xor r 1 - 52 = Nat.xor (r - 52) 1 ∧
    Nat.xor (r - 52) 1 < 24 := by
  decide +kernel

theorem regE_xor {r : ℕ} (h1 : 52 ≤ r) (h2 : r < 76) : regE (Nat.xor r 1) = (regE r)⁻¹ := by
  obtain ⟨h3, h4, -⟩ := reg_tab r h2 h1
  have h5 : ¬ r < 10 := by omega
  have h6 : r - 52 < 24 := by omega
  unfold regE
  rw [if_neg h3, if_neg h5, h4, pairG_xor h6]

theorem wE_conj {h : List ℕ} (hh : wokK h = true) (v : List ℕ) :
    wE (appK h (appK v (rinvK h))) = wE h * wE v * (wE h)⁻¹ := by
  rw [appK_eq, appK_eq, wE_append, wE_append, ← mul_assoc]
  congr 1
  exact rinvK_prod regE h fun r hr => regE_xor (wokK_spec hh r hr).1 (wokK_spec hh r hr).2

theorem slice_of {x : ℕ} (hx : x < 31671) :
    x / 1024 < 31 ∧ x / 1024 * 1024 ≤ x ∧ x - x / 1024 * 1024 < slLen (x / 1024) := by
  refine ⟨by omega, Nat.div_mul_le_self x 1024, ?_⟩
  by_cases h : x / 1024 = 30
  · rw [h]
    change x - 30 * 1024 < 951
    omega
  · have hb : Nat.beq (x / 1024) 30 = false :=
      Bool.eq_false_iff.2 fun hb => h (Nat.eq_of_beq_eq_true hb)
    unfold slLen
    rw [hb]
    change x - x / 1024 * 1024 < 1024
    omega

theorem slLen_ne {s : ℕ} (h : s ≠ 30) : slLen s = 1024 := by
  have hb : Nat.beq s 30 = false := Bool.eq_false_iff.2 fun hb => h (Nat.eq_of_beq_eq_true hb)
  unfold slLen
  rw [hb]
  all_goals rfl

theorem all_of_slices {f : ℕ → Bool} (h : ∀ s < 31, allBlk (Nat.mul s 1024) f (slLen s) = true)
    {x : ℕ} (hx : x < 31671) : f x = true := by
  obtain ⟨h1, -, h3⟩ := slice_of hx
  have e := CFSG.KS.allBlk_spec (h _ h1) _ h3
  have e2 : Nat.add (Nat.mul (x / 1024) 1024) (x - x / 1024 * 1024) = x := by
    change x / 1024 * 1024 + (x - x / 1024 * 1024) = x
    omega
  rwa [e2] at e

theorem all_of_blk {f : ℕ → Bool} {b c : ℕ} (hb : 0 < b)
    (h : ∀ s < c, allBlk (Nat.mul s b) f b = true) : ∀ i < c * b, f i = true := by
  intro i hi
  have hs : i / b < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)
  have e := CFSG.KS.allBlk_spec (h _ hs) (i % b) (Nat.mod_lt _ hb)
  have e2 : Nat.add (Nat.mul (i / b) b) (i % b) = i := by
    change i / b * b + i % b = i
    exact Nat.div_add_mod' i b
  rwa [e2] at e

theorem rootK_ne {PAR : ℕ → ℕ} {f k : ℕ} (hk : k ≠ 0) :
    rootK PAR (f + 1) k = rootK PAR f (PAR k) := by
  have hb : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun hb => hk (Nat.eq_of_beq_eq_true hb)
  change Bool.rec (motive := fun _ => Bool) (rootK PAR f (PAR k)) true (Nat.beq k 0) = _
  rw [hb]
  all_goals rfl

theorem climb0_zero {PAR LAB F : ℕ → ℕ} (f x : ℕ) : climb0 PAR LAB F (f + 1) 0 x = x := rfl

theorem climb0_ne {PAR LAB F : ℕ → ℕ} {f k : ℕ} (x : ℕ) (hk : k ≠ 0) :
    climb0 PAR LAB F (f + 1) k x = climb0 PAR LAB F f (PAR k) (tb F (52 + Nat.xor (LAB k) 1) x) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN (PAR k) fun p =>
    strictN (tb F (Nat.add 52 (Nat.xor (LAB k) 1)) x) fun y => climb0 PAR LAB F f p y) x
    (Nat.beq k 0) = _
  rw [nRec_eq, if_neg (by rw [Nat.beq_eq]; exact hk), sN_eq, sN_eq]
  all_goals rfl

theorem pos_spec {x : ℕ} (h : posK G POS0 PTS0 PAR0 LAB0 x = true) :
    (POS0 x < 31671 ∧ PTS0 (POS0 x) = x) ∧ rootK PAR0 20 x = true ∧
      edgeK G PTS0 PAR0 LAB0 x = true := by
  unfold posK at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  rw [sB_eq] at h1
  obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
  exact ⟨⟨Eq.mp Nat.blt_eq h5, Nat.eq_of_beq_eq_true h6⟩, h3, h4⟩

theorem edge_zero (h : edgeK G PTS0 PAR0 LAB0 0 = true) : PTS0 0 = 0 :=
  Nat.eq_of_beq_eq_true h

theorem edge_ne {k : ℕ} (hk : k ≠ 0) (h : edgeK G PTS0 PAR0 LAB0 k = true) :
    PAR0 k < 31671 ∧ LAB0 k < 24 ∧ tb G (52 + LAB0 k) (PTS0 (PAR0 k)) = PTS0 k := by
  have hb : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun hb => hk (Nat.eq_of_beq_eq_true hb)
  unfold edgeK at h
  rw [hb] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  exact ⟨Eq.mp Nat.blt_eq h1, Eq.mp Nat.blt_eq h3, Nat.eq_of_beq_eq_true h4⟩

theorem xor_lt : ∀ l < 24, Nat.xor l 1 < 24 := by decide +kernel

theorem climb_spec (hp : ∀ x < 31671, posK G POS0 PTS0 PAR0 LAB0 x = true) :
    ∀ f k, k < 31671 → rootK PAR0 f k = true → ∃ u : CFSG.Sporadic.Fi23.J, idx 31671 u 0 = PTS0 k ∧
      ∀ x < 31671, climb0 PAR0 LAB0 G f k x = idx 31671 u⁻¹ x := by
  have h0 : PTS0 0 = 0 := edge_zero (pos_spec (hp 0 (by norm_num))).2.2
  intro f
  induction f with
  | zero =>
    intro k _ hr
    have hk0 : k = 0 := Nat.eq_of_beq_eq_true hr
    subst hk0
    refine ⟨1, by rw [idx_one, h0], fun x _ => ?_⟩
    rw [inv_one, idx_one]
    rfl
  | succ f ih =>
    intro k hk hr
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨1, by rw [idx_one, h0], fun x _ => ?_⟩
      rw [inv_one, idx_one, climb0_zero]
    · obtain ⟨hpa, hla, he⟩ := edge_ne hk0 (pos_spec (hp k hk)).2.2
      rw [rootK_ne hk0] at hr
      obtain ⟨u, hu0, hu⟩ := ih (PAR0 k) hpa hr
      refine ⟨pairG gs (LAB0 k) * u, ?_, fun x hx => ?_⟩
      · rw [idx_mul, hu0, letter_acts hla (PTS0 (PAR0 k)) (hu0 ▸ idx_lt u (by norm_num))]
        exact he
      · rw [climb0_ne x hk0, ← letter_acts (xor_lt _ hla) x hx, pairG_xor hla,
          hu _ (idx_lt _ hx), ← idx_mul, mul_inv_rev]

theorem hD43 : ∀ y < 31671, tb G 43 y = idx 31671 d y := by
  intro y hy
  have e : tA G 0 y = tb G 43 y := rfl
  rw [← e, tA_eq (by norm_num) hy, conjPt_zero]

theorem rel_spec (hp : ∀ x < 31671, posK G POS0 PTS0 PAR0 LAB0 x = true) {v x : ℕ}
    (hv : v < 31671) (hx : x < 31671) :
    relK POS0 PAR0 LAB0 G v x = true ↔ conjPt v * conjPt x = conjPt x * conjPt v := by
  obtain ⟨⟨hk, hpk⟩, -, -⟩ := pos_spec (hp v hv)
  obtain ⟨u, hu0, hu⟩ := climb_spec hp 20 (POS0 v) hk (pos_spec (hp _ hk)).2.1
  exact relK_spec hD43 hx (hu0.trans hpk) (hu x hx)

theorem pass_iff (hp : ∀ x < 31671, posK G POS0 PTS0 PAR0 LAB0 x = true)
    {S : List (List ℕ × Bool)} (hS : ∀ s ∈ S, WOK s.1) {v : ℕ} (hv : v < 31671) :
    passK POS0 PAR0 LAB0 G S v = true ↔ ∀ s ∈ S, (conjPt v * conjPt (idx 31671 (wE s.1) v) =
      conjPt (idx 31671 (wE s.1) v) * conjPt v ↔ s.2 = true) := by
  rw [passK_spec]
  refine forall₂_congr fun s hs => ?_
  rw [wv_eq (hS s hs) hv, ← rel_spec hp hv (idx_lt _ hv)]
  exact Bool.eq_iff_iff

theorem memK_iff (l : List ℕ) (x : ℕ) : memK l x = true ↔ x ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons p l ih =>
    change Bool.rec (motive := fun _ => Bool) (memK l x) true (Nat.beq p x) = true ↔ _
    rw [bRec_eq, List.mem_cons]
    by_cases h : p = x
    · rw [if_pos (beq_true h)]
      exact ⟨fun _ => Or.inl h.symm, fun _ => rfl⟩
    · rw [if_neg fun hb => h (Nat.eq_of_beq_eq_true hb), ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left fun e => h e.symm⟩

theorem newK_eq (l : List ℕ) (x : ℕ) : newK l x = if x ∈ l then 0 else 1 := by
  unfold newK
  rw [nRec_eq]
  by_cases h : x ∈ l
  · rw [if_pos ((memK_iff l x).2 h), if_pos h]
  · rw [if_neg (mt (memK_iff l x).1 h), if_neg h]

theorem card_step (s : Finset ℕ) (l : List ℕ) (hs : ∀ y, y ∈ s ↔ y ∈ l) (x : ℕ) :
    (insert x s).card = s.card + newK l x := by
  rw [newK_eq, Finset.card_insert_eq_ite]
  by_cases h : x ∈ l
  · rw [if_pos ((hs x).2 h), if_pos h, add_zero]
  · rw [if_neg (mt (hs x).1 h), if_neg h]

theorem cnt5_card (v a b c e : ℕ) :
    cnt5K v a b c e = (insert e (insert c (insert b (insert a ({v} : Finset ℕ))))).card := by
  have h1 : ∀ y, y ∈ ({v} : Finset ℕ) ↔ y ∈ [v] := fun y => by simp
  have h2 : ∀ y, y ∈ insert a ({v} : Finset ℕ) ↔ y ∈ [v, a] := fun y => by
    simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.mem_nil_iff, or_false]
    tauto
  have h3 : ∀ y, y ∈ insert b (insert a ({v} : Finset ℕ)) ↔ y ∈ [v, a, b] := fun y => by
    simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.mem_nil_iff, or_false]
    tauto
  have h4 : ∀ y, y ∈ insert c (insert b (insert a ({v} : Finset ℕ))) ↔ y ∈ [v, a, b, c] :=
    fun y => by
      simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.mem_nil_iff,
        or_false]
      tauto
  unfold cnt5K
  rw [card_step _ _ h4, card_step _ _ h3, card_step _ _ h2, card_step _ _ h1,
    Finset.card_singleton]
  all_goals rfl

theorem exists_four {Q : Subgroup CFSG.Sporadic.Fi23.J} {k : ℕ} (S : Finset ℕ) (hS : 4 ≤ S.card)
    (h : ∀ s ∈ S, ∃ y ∈ Q, idx 31671 y k = s) :
    ∃ f : Fin 4 → CFSG.Sporadic.Fi23.J, (∀ i, f i ∈ Q) ∧ Function.Injective fun i => idx 31671 (f i) k := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
  let e : Fin 4 ≃ T := (T.equivFinOfCardEq hT).symm
  choose y hyQ hyk using fun i : Fin 4 => h (e i) (hTS (e i).2)
  refine ⟨y, hyQ, fun i j hij => e.injective (Subtype.ext ?_)⟩
  simp only at hij
  rw [← hyk i, ← hyk j, hij]

end CertificateChecks.KernelFi23Nt

end
