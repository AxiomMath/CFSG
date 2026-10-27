module

public import Certificates.Kernel.TwoHSLe4.TFDefs
public import Certificates.Kernel.TwoHSLe4.RawB

public section

namespace CertificateChecks.KernelTwoHSLe4.TF

open CFSG.EvenSporadicStandard.TwoHS

@[expose] def allL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec true (fun b _ ih => p b && ih) l

theorem allL_iff {α : Type} {p : α → Bool} {l : List α} :
    allL p l = true ↔ ∀ b ∈ l, p b = true := by
  induction l with
  | nil => simp [allL]
  | cons b l ih =>
    change (p b && allL p l) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

@[expose] def anyL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec false (fun b _ ih => p b || ih) l

theorem anyL_iff {α : Type} {p : α → Bool} {l : List α} :
    anyL p l = true ↔ ∃ b ∈ l, p b = true := by
  induction l with
  | nil => simp [anyL]
  | cons b l ih =>
    change (p b || anyL p l) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp

@[expose] def r4k (a b : R4) : Bool :=
  Nat.beq a.a00 b.a00 && Nat.beq a.a01 b.a01 && Nat.beq a.a02 b.a02 && Nat.beq a.a03 b.a03 &&
  Nat.beq a.a10 b.a10 && Nat.beq a.a11 b.a11 && Nat.beq a.a12 b.a12 && Nat.beq a.a13 b.a13 &&
  Nat.beq a.a20 b.a20 && Nat.beq a.a21 b.a21 && Nat.beq a.a22 b.a22 && Nat.beq a.a23 b.a23 &&
  Nat.beq a.a30 b.a30 && Nat.beq a.a31 b.a31 && Nat.beq a.a32 b.a32 && Nat.beq a.a33 b.a33

theorem r4k_iff {a b : R4} : r4k a b = true ↔ a = b := by
  cases a
  cases b
  simp [r4k, Nat.beq_eq, and_assoc]

@[expose] def memK (x : R4) (l : List R4) : Bool :=
  List.rec false (fun b _ ih => r4k x b || ih) l

theorem memK_iff {x : R4} {l : List R4} : memK x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memK]
  | cons b l ih =>
    change (r4k x b || memK x l) = true ↔ _
    rw [Bool.or_eq_true, r4k_iff, ih, List.mem_cons]

@[expose] def keyH (a : R4) : Nat :=
  Nat.add a.a00 (Nat.mul 4 (Nat.add a.a01 (Nat.mul 4 (Nat.add a.a02 (Nat.mul 4 (Nat.add a.a03
  (Nat.mul 4 (Nat.add a.a10 (Nat.mul 4 (Nat.add a.a11 (Nat.mul 4 (Nat.add a.a12 (Nat.mul 4
  (Nat.add a.a13 (Nat.mul 4 (Nat.add a.a20 (Nat.mul 4 (Nat.add a.a21 (Nat.mul 4 (Nat.add a.a22
  (Nat.mul 4 (Nat.add a.a23 (Nat.mul 4 (Nat.add a.a30 (Nat.mul 4 (Nat.add a.a31 (Nat.mul 4
  (Nat.add a.a32 (Nat.mul 4 a.a33)))))))))))))))))))))))))))))

@[expose] def bitB (M i : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 i))

@[expose] def selB (c x y : Bool) : Bool := Bool.rec y x c

@[expose] def memQ (M P : Nat) (x : R4) (l : List R4) : Bool :=
  selB (bitB M (Nat.mod (keyH x) P)) (memK x l) false

theorem memQ_eq {M P : Nat} {l : List R4} (hM : allL (fun t => bitB M (Nat.mod (keyH t) P)) l = true)
    (x : R4) : memQ M P x l = memK x l := by
  unfold memQ
  cases hb : bitB M (Nat.mod (keyH x) P)
  · cases hx : memK x l
    · rfl
    · have h' : bitB M (Nat.mod (keyH x) P) = true := allL_iff.1 hM x (memK_iff.1 hx)
      rw [hb] at h'
      exact absurd h' Bool.false_ne_true
  · rfl

@[expose] def wfB (a : R4) : Bool :=
  Nat.blt a.a00 4 && Nat.blt a.a01 4 && Nat.blt a.a02 4 && Nat.blt a.a03 4 &&
  Nat.blt a.a10 4 && Nat.blt a.a11 4 && Nat.blt a.a12 4 && Nat.blt a.a13 4 &&
  Nat.blt a.a20 4 && Nat.blt a.a21 4 && Nat.blt a.a22 4 && Nat.blt a.a23 4 &&
  Nat.blt a.a30 4 && Nat.blt a.a31 4 && Nat.blt a.a32 4 && Nat.blt a.a33 4

theorem wfB_iff {a : R4} : wfB a = true ↔ a.wf := by
  cases a
  simp [wfB, R4.wf, Nat.blt_eq, and_assoc]

@[expose] def eqLR (l m : List R4) : Bool :=
  List.rec (motive := fun _ => List R4 → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b m' _ => r4eq a b && ih m') m)
    l m

theorem eqLR_eq : ∀ (l m : List R4), eqLR l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: l, b :: m, h => by
    change (r4eq a b && eqLR l m) = true at h
    rw [Bool.and_eq_true] at h
    rw [r4eq_iff.1 h.1, eqLR_eq l m h.2]

@[expose] def eqLV (l m : List RV) : Bool :=
  List.rec (motive := fun _ => List RV → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b m' _ => rveq a b && ih m') m)
    l m

theorem eqLV_eq : ∀ (l m : List RV), eqLV l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: l, b :: m, h => by
    change (rveq a b && eqLV l m) = true at h
    rw [Bool.and_eq_true] at h
    rw [rveq_iff.1 h.1, eqLV_eq l m h.2]

@[expose] def colR (l : List R4) : List R4 :=
  List.rec [] (fun a _ ih => Bool.rec (motive := fun _ => List R4) (a :: ih) ih (memK a ih)) l

theorem colR_eq : ∀ l : List R4, colR l = l.dedup
  | [] => rfl
  | a :: l => by
    change Bool.rec (motive := fun _ => List R4) (a :: colR l) (colR l) (memK a (colR l)) = _
    rw [colR_eq l]
    cases h : memK a l.dedup
    · refine (List.dedup_cons_of_notMem' fun ha => ?_).symm
      rw [memK_iff.2 ha] at h
      simp at h
    · exact (List.dedup_cons_of_mem' (memK_iff.1 h)).symm

@[expose] def colV (l : List RV) : List RV :=
  List.rec [] (fun a _ ih => Bool.rec (motive := fun _ => List RV) (a :: ih) ih (memV a ih)) l

theorem colV_eq : ∀ l : List RV, colV l = l.dedup
  | [] => rfl
  | a :: l => by
    change Bool.rec (motive := fun _ => List RV) (a :: colV l) (colV l) (memV a (colV l)) = _
    rw [colV_eq l]
    cases h : memV a l.dedup
    · refine (List.dedup_cons_of_notMem' fun ha => ?_).symm
      rw [memV_iff.2 ha] at h
      simp at h
    · exact (List.dedup_cons_of_mem' (memV_iff.1 h)).symm

@[expose] def subLR (l m : List R4) : Bool :=
  List.rec (motive := fun _ => List R4 → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun b _ ih l => List.rec (motive := fun _ => Bool) true
      (fun a l' _ => selB (r4eq a b) (ih l') (ih l)) l) m l

theorem subLR_sub : ∀ (m l : List R4), subLR l m = true → ∀ x ∈ l, x ∈ m
  | [], [], _ => by simp
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _ => by simp
  | b :: m, a :: l', h => by
    revert h
    change selB (r4eq a b) (subLR l' m) (subLR (a :: l') m) = true → _
    cases hab : r4eq a b
    · intro h x hx
      exact List.mem_cons.2 (Or.inr (subLR_sub m (a :: l') h x hx))
    · intro h x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons.2 (Or.inl (r4eq_iff.1 hab))
      · exact List.mem_cons.2 (Or.inr (subLR_sub m l' h x hx))

@[expose] def treeK (gl : List R4) (tb : List (R4 × R4 × R4)) (acc : List R4) : Bool :=
  List.rec (motive := fun _ => List R4 → Bool) (fun _ => true)
    (fun e _ ih acc => (r4eq e.1 R4.one ||
      (memR e.2.1 acc && memR e.2.2 gl && r4eq (rmul e.2.1 e.2.2) e.1)) && ih (e.1 :: acc)) tb acc

theorem treeK_sound {P : R4 → Prop} {gl : List R4} (h1 : P R4.one)
    (hg : ∀ y, P y → ∀ g ∈ gl, P (rmul y g)) :
    ∀ (tb : List (R4 × R4 × R4)) (acc : List R4), (∀ y ∈ acc, P y) → treeK gl tb acc = true →
      ∀ e ∈ tb, P e.1
  | [], _, _, _ => by simp
  | e :: tb, acc, hacc, h => by
    change ((r4eq e.1 R4.one || (memR e.2.1 acc && memR e.2.2 gl &&
      r4eq (rmul e.2.1 e.2.2) e.1)) && treeK gl tb (e.1 :: acc)) = true at h
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h0, ht⟩ := h
    have he : P e.1 := by
      rcases h0 with h0 | ⟨⟨hy, hgm⟩, hx⟩
      · rw [r4eq_iff.1 h0]
        exact h1
      · rw [← r4eq_iff.1 hx]
        exact hg _ (hacc _ (memR_iff.1 hy)) _ (memR_iff.1 hgm)
    have hacc' : ∀ y ∈ e.1 :: acc, P y := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact he
      · exact hacc y hy
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact he
    · exact treeK_sound h1 hg tb (e.1 :: acc) hacc' ht e' he'

@[expose] def nrmK (tl w : List R4) (M P : Nat) (sr si : List R4) : Bool :=
  List.rec (motive := fun _ => List R4 → Bool) (fun _ => true)
    (fun b _ ih si => List.rec (motive := fun _ => Bool) false
      (fun bi si' _ => (memQ M P b tl || (r4k (rmul b bi) R4.one &&
        anyL (fun a => !memQ M P (rmul (rmul b a) bi) tl) w)) && ih si') si) sr si

theorem nrmK_sound {tl w : List R4} {M P : Nat}
    (hM : allL (fun t => bitB M (Nat.mod (keyH t) P)) tl = true) :
    ∀ (sr si : List R4), nrmK tl w M P sr si = true →
    ∀ b ∈ sr, b ∈ tl ∨ ∃ bi, rmul b bi = R4.one ∧ ∃ a ∈ w, rmul (rmul b a) bi ∉ tl
  | [], _, _ => by simp
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | b :: sr, bi :: si, h => by
    change ((memQ M P b tl || (r4k (rmul b bi) R4.one &&
      anyL (fun a => !memQ M P (rmul (rmul b a) bi) tl) w)) && nrmK tl w M P sr si) = true at h
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, anyL_iff] at h
    obtain ⟨h0, ht⟩ := h
    intro b' hb'
    rcases List.mem_cons.1 hb' with hbb | hb'
    · rw [hbb]
      rcases h0 with h0 | ⟨h1, a, ha, h2⟩
      · rw [memQ_eq hM] at h0
        exact Or.inl (memK_iff.1 h0)
      · refine Or.inr ⟨bi, r4k_iff.1 h1, a, ha, fun hm => ?_⟩
        have h2' : (!memQ M P (rmul (rmul b a) bi) tl) = true := h2
        rw [memQ_eq hM, memK_iff.2 hm] at h2'
        simp at h2'
    · exact nrmK_sound hM sr si ht b' hb'

theorem rmul_assoc (a b c : R4) : rmul (rmul a b) c = rmul a (rmul b c) :=
  ofR4_inj (wf_rmul _ _) (wf_rmul _ _) (by rw [ofR4_rmul, ofR4_rmul, ofR4_rmul, ofR4_rmul, mul_assoc])

theorem rmul_one' {a : R4} (ha : a.wf) : rmul a R4.one = a :=
  ofR4_inj (wf_rmul _ _) ha (by rw [ofR4_rmul, ofR4_one, mul_one])

theorem one_rmul' {a : R4} (ha : a.wf) : rmul R4.one a = a :=
  ofR4_inj (wf_rmul _ _) ha (by rw [ofR4_rmul, ofR4_one, one_mul])

@[expose] def starB (vd : List RV) (tl : List R4) : Bool :=
  allL (fun b => r4eq b R4.one || !r4eq (rmul b b) R4.one ||
    Nat.ble 5 (colV (vd.map fun v => rmv (rsub1 b) v)).length) tl

theorem imCardR_ge {vd : List RV} (hvd : allL (fun v => memV v allVR) vd = true) (c : R4) :
    (vd.map fun v => rmv (rsub1 c) v).dedup.length ≤ imCardR c := by
  refine ((List.nodup_dedup _).subperm fun x hx => ?_).length_le
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hx)
  exact List.mem_dedup.2 (List.mem_map.2 ⟨v, memV_iff.1 (allL_iff.1 hvd v hv), rfl⟩)

theorem traw_of {sr tl gl ts w si sh : List R4} {tb : List (R4 × R4 × R4)} {f om vd : List RV}
    {t : RV} {M P : Nat} (hsh : shatR = sh) (hf : fR = f) (hom : omR = om) (ht : tRV = t)
    (hvd : allL (fun v => memV v allVR) vd = true)
    (h1 : allL wfB sr = true) (h2 : allL wfB tl = true) (h4 : memR R4.one tl = true)
    (h5a : allL (fun a => allL (fun g => memK (rmul a g) tl) gl) tl = true)
    (h5b : treeK gl tb [] = true) (h5c : allL (fun x => anyL (fun e => r4eq e.1 x) tb) tl = true)
    (h7a : subLR ts sr = true) (h7b : allL (fun a => memR a ts) tl = true)
    (h8 : allL (fun s => memR s tl) sh = true)
    (h9 : allL (fun a => r4eq (rpow2 7 a) R4.one) tl = true) (h10 : starB vd tl = true)
    (h11 : allL (fun v => Nat.ble (colV (tl.map fun a => rmv a v)).length 4) f = true)
    (h12 : allL (fun v => Nat.blt 4 (colV (tl.map fun a => rmv a (radd t v))).length) f = true)
    (h13 : allL (fun v => anyL (fun a => rveq (rmv a t) (radd t v)) tl) f = true)
    (h14 : allL (fun a => !allL (fun v => rveq (rmv a v) v) f || r4eq (rmul a a) R4.one) tl = true)
    (h15 : allL (fun a => !allL (fun v => rveq (rmv a v) v) om || r4eq a R4.one ||
      r4eq a R4.negOne) tl = true)
    (h16 : allL (fun a => !rveq (rmv a t) t || memR a sh) tl = true)
    (h17a : allL (fun a => memR a tl) w = true)
    (hM : allL (fun t => bitB M (Nat.mod (keyH t) P)) tl = true) (h17 : nrmK tl w M P sr si = true) :
    TRaw sr tl (invPairsR tl) := by
  have hwf : ∀ a ∈ tl, a.wf := fun a ha => wfB_iff.1 (allL_iff.1 h2 a ha)
  have hone : R4.one ∈ tl := memR_iff.1 h4
  have hP := treeK_sound (P := fun x => ∀ a ∈ tl, rmul a x ∈ tl)
    (fun a ha => by rw [rmul_one' (hwf a ha)]; exact ha)
    (fun y hy g hg a ha => by
      rw [← rmul_assoc]
      have h := allL_iff.1 h5a _ (hy a ha)
      exact memK_iff.1 (allL_iff.1 h g hg))
    tb [] (by simp) h5b
  have hmul : ∀ a ∈ tl, ∀ b ∈ tl, rmul a b ∈ tl := by
    intro a ha b hb
    obtain ⟨e, he, hx⟩ := anyL_iff.1 (allL_iff.1 h5c b hb)
    rw [← r4eq_iff.1 hx]
    exact hP e he a ha
  have hpow : ∀ a ∈ tl, rpow2 7 a = R4.one := fun a ha => r4eq_iff.1 (allL_iff.1 h9 a ha)
  have hip : ∀ p ∈ invPairsR tl, p.1 ∈ tl ∧ p.2 ∈ tl ∧ rmul p.1 p.2 = R4.one := by
    intro p hp
    simp only [invPairsR, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    obtain ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩ := hp
    exact ⟨ha, hb, hab⟩
  have hone_ip : (R4.one, R4.one) ∈ invPairsR tl :=
    List.mem_flatMap.2 ⟨R4.one, hone, List.mem_map.2 ⟨R4.one, List.mem_filter.2 ⟨hone, by
      rw [rmul_one' wf_one]
      exact beq_self_eq_true _⟩, rfl⟩⟩
  unfold TRaw
  rw [hsh, hf, hom, ht]
  refine ⟨fun a ha => wfB_iff.1 (allL_iff.1 h1 a ha), hwf, hip, hone, hmul, ?_, ?_,
    fun s hs => memR_iff.1 (allL_iff.1 h8 s hs), hpow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hm : ∀ n : ℕ, (fun x => rmul x a)^[n] R4.one ∈ tl := by
      intro n
      induction n with
      | zero => exact hone
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hmul _ ih _ ha
    have hv : ∀ n : ℕ, ofR4 ((fun x => rmul x a)^[n] R4.one) = ofR4 a ^ n := by
      intro n
      induction n with
      | zero => simp [ofR4_one]
      | succ n ih => rw [Function.iterate_succ_apply', ofR4_rmul, ih, pow_succ]
    refine ⟨_, hm 127, ofR4_inj (wf_rmul _ _) wf_one ?_⟩
    have h128 := ofR4_rpow2 7 a
    rw [hpow a ha, ofR4_one] at h128
    rw [ofR4_rmul, hv, ofR4_one, ← pow_succ']
    exact h128.symm
  · intro a ha
    exact memR_iff.1 (allL_iff.1 h7b a ha) |> subLR_sub sr ts h7a a
  · intro b hb hb1 hbb
    have hbw := hwf b hb
    have hx : (r4eq b R4.one || !r4eq (rmul b b) R4.one ||
        Nat.ble 5 (colV (vd.map fun v => rmv (rsub1 b) v)).length) = true :=
      allL_iff.1 h10 b hb
    rw [Bool.or_eq_true, Bool.or_eq_true] at hx
    rcases hx with (hx | hx) | hx
    · exact absurd (r4eq_iff.1 hx) hb1
    · rw [r4eq_iff.2 hbb] at hx
      simp at hx
    · right
      rw [Nat.ble_eq, colV_eq] at hx
      have hmem : b ∈ conjR (invPairsR tl) b := by
        refine List.mem_dedup.2 (List.mem_map.2 ⟨(R4.one, R4.one), hone_ip, ?_⟩)
        change rmul (rmul R4.one b) R4.one = b
        rw [one_rmul' hbw, rmul_one' hbw]
      exact le_trans hx (le_trans (imCardR_ge hvd b)
        (List.le_sum_of_mem (List.mem_map.2 ⟨b, hmem, rfl⟩)))
  · intro v hv
    have hx : Nat.ble (colV (tl.map fun a => rmv a v)).length 4 = true := allL_iff.1 h11 v hv
    rw [Nat.ble_eq, colV_eq] at hx
    exact hx
  · intro v hv
    have hx : Nat.blt 4 (colV (tl.map fun a => rmv a (radd t v))).length = true :=
      allL_iff.1 h12 v hv
    rw [Nat.blt_eq, colV_eq] at hx
    exact hx
  · intro v hv
    obtain ⟨a, ha, hx⟩ := anyL_iff.1 (allL_iff.1 h13 v hv)
    exact ⟨a, ha, rveq_iff.1 hx⟩
  · intro a ha hfix
    have hx : (!allL (fun v => rveq (rmv a v) v) f || r4eq (rmul a a) R4.one) = true :=
      allL_iff.1 h14 a ha
    rw [allL_iff.2 (fun v hv => rveq_iff.2 (hfix v hv))] at hx
    simp only [Bool.not_true, Bool.false_or] at hx
    exact r4eq_iff.1 hx
  · intro a ha hfix
    have hx : (!allL (fun v => rveq (rmv a v) v) om || r4eq a R4.one || r4eq a R4.negOne) = true :=
      allL_iff.1 h15 a ha
    rw [allL_iff.2 (fun v hv => rveq_iff.2 (hfix v hv))] at hx
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact Or.inl (r4eq_iff.1 hx)
    · exact Or.inr (r4eq_iff.1 hx)
  · intro a ha hat
    have hx : (!rveq (rmv a t) t || memR a sh) = true := allL_iff.1 h16 a ha
    rw [rveq_iff.2 hat] at hx
    simp only [Bool.not_true, Bool.false_or] at hx
    exact memR_iff.1 hx
  · intro b hb
    rcases nrmK_sound hM sr si h17 b hb with h | ⟨bi, hbi, a, ha, hc⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, memR_iff.1 (allL_iff.1 h17a a ha), fun a' ha' he => hc ?_⟩
      rw [he, rmul_assoc, hbi, rmul_one' (hwf a' ha')]
      exact ha'

end CertificateChecks.KernelTwoHSLe4.TF
