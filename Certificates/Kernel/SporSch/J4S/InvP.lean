
module

public import Certificates.Kernel.SporSch.J4S.InvA
public import CFSG.Certificates.Kernel.SporSch.J4SGetSound
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4InvP

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Eta CertificateChecks.KernelSporSch.J4InvC
open CertificateChecks.KernelSporSch.J4InvW CertificateChecks.KernelSporSch.J4InvA

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem nb_iff (a b : Bool) : notB (Bool.rec (motive := fun _ => Bool) false b a) = true ↔
    ¬ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem bIf_t {c t e : Bool} (h : c = true) : Bool.rec (motive := fun _ => Bool) e t c = t := by
  subst h
  rfl

theorem bIf_f {c t e : Bool} (h : c = false) : Bool.rec (motive := fun _ => Bool) e t c = e := by
  subst h
  rfl

theorem nIf_t {c : Bool} {t e : Nat} (h : c = true) : Bool.rec (motive := fun _ => Nat) e t c = t := by
  subst h
  rfl

theorem nIf_f {c : Bool} {t e : Nat} (h : c = false) : Bool.rec (motive := fun _ => Nat) e t c = e := by
  subst h
  rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.J4Q.strictB y k = k y := by
  cases y <;> rfl

theorem slice_spec {k S : Nat} {f : Nat → Bool} (hk : 0 < k)
    (h : ∀ s < S, allBlk (Nat.mul k s) f k = true) : ∀ j < k * S, f j = true := by
  intro j hj
  have hs : j / k < S := (Nat.div_lt_iff_lt_mul hk).2 (by rwa [Nat.mul_comm])
  have := allBlk_spec (h _ hs) (j % k) (Nat.mod_lt j hk)
  rwa [show Nat.add (Nat.mul k (j / k)) (j % k) = j from Nat.div_add_mod j k] at this

theorem anyK_spec {f : Nat → Bool} : ∀ {n : Nat}, anyK n f = true → ∃ i < n, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    cases hf : f n
    · have h' : Bool.rec (motive := fun _ => Bool) (anyK n f) true (f n) = true := h
      rw [hf] at h'
      obtain ⟨i, hi, hfi⟩ := anyK_spec h'
      exact ⟨i, by omega, hfi⟩
    · exact ⟨n, by omega, hf⟩

theorem F_get {j k : Nat} (hj : j < 19967) (hk : k < 4) : (invForest[j]!)[k]! = FF k j := by
  rw [invForest, J4IF.eq, CFSG.KS.SporSch.tokK_sound J4IF.tok, (permsK_sound pF).2 j hj,
    unpackW_get hk]
  rfl

theorem C_get {i e : Nat} (hi : i < 4) (he : e < 1024) : (conjTab[i]!)[e]! = CT i e := by
  rw [conjTab, J4IC.eq, CFSG.KS.SporSch.tokK_sound J4IC.tok, (permsK_sound pC).2 i hi,
    unpackW_get he]
  rfl

theorem A_get {i k : Nat} (hi : i < 77) (hk : k < 3) : (ambHead[i]!)[k]! = AH k i := by
  rw [ambHead, J4AH.eq, CFSG.KS.SporSch.tokK_sound J4AH.tok, (permsK_sound pA).2 i hi,
    unpackW_get hk]
  rfl

theorem aw_eq : ambWords = J4AW.ws.toArray := by
  rw [ambWords, J4AW.eq, CFSG.KS.SporSch.tokK_sound J4AW.tok]
  exact tokWords_sound J4AW.wtok

theorem getW_eq : ∀ (L : List (List Int)) (i : Nat), L[i]?.getD [] = getW L i
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    rw [List.getElem?_cons_succ]
    exact getW_eq L i

theorem aw_get (i : Nat) : ambWords[i]! = getW J4AW.ws i := by
  rw [aw_eq, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, ← getW_eq]
  rfl

theorem GI_eq {i : Nat} (hi : i < 4) : genInvColumns[i]! = unpack11 (J4GI i) :=
  (bind2_sound J4GI.bind).2 i hi

theorem SQ_get {e : Nat} (he : e < 1024) : squares[e]! = J4SQ.T e := by
  rw [J4Five.SQ_eq, tabA_get he]

theorem fN_eq {j : Nat} (hj : j < 19967) : fN j = FF 0 j := F_get hj (by omega)
theorem fE_eq {j : Nat} (hj : j < 19967) : fE j = FF 1 j := F_get hj (by omega)
theorem fP_eq {j : Nat} (hj : j < 19967) : fP j = FF 2 j := F_get hj (by omega)
theorem fG_eq {j : Nat} (hj : j < 19967) : fG j = FF 3 j := F_get hj (by omega)

theorem fix_iff {n e : Nat} (he : e < 1024) : fixK n e = true ↔
    (squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧ ¬ (n = 0 ∧ e = 0)) := by
  unfold fixK
  rw [bAnd_iff, bAnd_iff, nb_iff, beq_iff, beq_iff, beq_iff, beq_iff, SQ_get he,
    J4Five.E_eq he, app_eq]

theorem gN_eq {g n e : Nat} (hg : g < 5) (he : e < 1024) : genMapN g n e = gN g n e := by
  unfold genMapN gN
  by_cases h0 : g = 0
  · subst h0
    rw [ite_eq_left rfl, J4Five.E_eq he, app_eq]
    rfl
  · rw [ite_eq_right h0, J4Five.GC_eq (by omega), app_eq, nIf_f (beqF h0)]
    rfl

theorem gE_eq {g e : Nat} (hg : g < 5) (he : e < 1024) : genMapE g e = gE g e := by
  unfold genMapE gE
  by_cases h0 : g = 0
  · subst h0
    rfl
  · rw [ite_eq_right h0, C_get (by omega) he, nIf_f (beqF h0)]
    rfl

theorem amb_lt {n e : Nat} (h : ambK n e = true) : ambIdx n e < 77 := by
  obtain ⟨i, hi, hm⟩ := anyK_spec h
  obtain ⟨h0, h1⟩ := (bAnd_iff _ _).1 hm
  have hp : ((ambHead[i]!)[0]! == n && (ambHead[i]!)[1]! == e) = true := by
    rw [A_get hi (by omega), A_get hi (by omega), beq_iff.1 h0, beq_iff.1 h1]
    simp
  have hs : ((List.range 77).find? fun i =>
      (ambHead[i]!)[0]! == n && (ambHead[i]!)[1]! == e).isSome :=
    List.find?_isSome.2 ⟨i, List.mem_range.2 hi, hp⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
  rw [ambIdx, hx, Option.getD_some]
  exact List.mem_range.1 (List.mem_of_find?_eq_some hx)

theorem recK_all : ∀ j < 19967, recK j = true := fun j hj =>
  slice_spec (k := 1024) (S := 20) (by omega) J4IR.all j (by omega)

theorem rec_ok {j : Nat} (hj : j < 19967) :
    (fN j < 2048 ∧ fE j < 1024 ∧ squares[fE j]! = 0 ∧
      app11 elementColumns[fE j]! (fN j) = fN j ∧ ¬ (fN j = 0 ∧ fE j = 0)) ∧
    ((fP j = j ∧ (fE j = 0 ∨ ambIdx (fN j) (fE j) < 77)) ∨
      (fP j < j ∧ fG j < 5 ∧ genMapN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧
        genMapE (fG j) (fE (fP j)) = fE j)) := by
  have h := recK_all j hj
  unfold recK at h
  rw [bIf_t (blt_iff.2 hj)] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  have l1 := blt_iff.1 h1
  have l2 := blt_iff.1 h2
  rw [fN_eq hj, fE_eq hj, fP_eq hj, fG_eq hj]
  refine ⟨⟨l1, l2, (fix_iff l2).1 h3⟩, ?_⟩
  by_cases hp : FF 2 j = j
  · rw [bIf_t (beq_iff.2 hp)] at h
    refine Or.inl ⟨hp, ?_⟩
    by_cases he : FF 1 j = 0
    · exact Or.inl he
    · rw [bIf_f (beqF he)] at h
      exact Or.inr (amb_lt h)
  · rw [bIf_f (beqF hp)] at h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h
    have l4 := blt_iff.1 h4
    have l5 := blt_iff.1 h5
    have l6 := blt_iff.1 h6
    have hpj : FF 2 j < 19967 := by omega
    refine Or.inr ⟨l4, l5, ?_, ?_⟩
    · rw [fN_eq hpj, fE_eq hpj, gN_eq l5 l6]
      exact beq_iff.1 h7
    · rw [fE_eq hpj, gE_eq l5 l6]
      exact beq_iff.1 h8

@[expose] def key (j : Nat) : Nat := fN j + 2048 * fE j

theorem key_lt {j : Nat} (hj : j < 19967) : key j < 2048 * 1024 := by
  have h := (rec_ok hj).1
  unfold key
  omega

private theorem loop_fold (n : Nat) (a : Array Nat) (f e : Nat → Nat) :
    (Id.run do
      let mut a := a
      for j in [0:n] do
        a := a.set! (f j + 2048 * e j) (j + 1)
      return a) = (List.range n).foldl (fun a j => a.set! (f j + 2048 * e j) (j + 1)) a := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem fidx_fold : forestIdx = (List.range 19967).foldl (fun a j => a.set! (key j) (j + 1))
    (Array.replicate (2048 * 1024) 0) := by
  unfold forestIdx
  simp only [key]
  exact loop_fold 19967 (Array.replicate (2048 * 1024) 0) fN fE

theorem fold_inv : ∀ m ≤ 19967,
    ((List.range m).foldl (fun a j => a.set! (key j) (j + 1)) (Array.replicate (2048 * 1024) 0)).size
      = 2048 * 1024 ∧
    (∀ k < 2048 * 1024,
      ((List.range m).foldl (fun a j => a.set! (key j) (j + 1))
        (Array.replicate (2048 * 1024) 0))[k]! = 0 ∨
      ∃ j < m, ((List.range m).foldl (fun a j => a.set! (key j) (j + 1))
        (Array.replicate (2048 * 1024) 0))[k]! = j + 1 ∧ key j = k) ∧
    (∀ j < m, ((List.range m).foldl (fun a j => a.set! (key j) (j + 1))
        (Array.replicate (2048 * 1024) 0))[key j]! ≠ 0)
  | 0, _ => by
    refine ⟨by simp, fun k hk => Or.inl ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    simp [hk]
  | m + 1, hm => by
    obtain ⟨hs, hi, hn⟩ := fold_inv m (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set a := (List.range m).foldl (fun a j => a.set! (key j) (j + 1))
      (Array.replicate (2048 * 1024) 0)
    have hkm := key_lt (j := m) (by omega)
    refine ⟨by rw [Array.size_set!, hs], fun k hk => ?_, fun j hj => ?_⟩
    · by_cases e : key m = k
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hkm)]
        exact Or.inr ⟨m, by omega, rfl, rfl⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ e]
        rcases hi k hk with h | ⟨j, hj, h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, h1, h2⟩
    · by_cases e : key m = key j
      · rw [← e, Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hkm)]
        omega
      · rw [Array.getElem!_set!_ne _ _ _ _ e]
        have hjm : j < m := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
          · exact h
          · exact absurd (congrArg key h.symm) e
        exact hn j hjm

@[expose] noncomputable def fxR (P a k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
      (nat_lit 1), Nat.xor s (colK P j), s))) k

theorem fxR_succ (P a k : Nat) : fxR P a (k + 1) =
    if a.testBit k then fxR P a k ^^^ colK P k else fxR P a k := by
  have e : Nat.land (Nat.shiftRight a k) 1 = a / 2 ^ k % 2 := by
    change (a >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hb : Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1)) (nat_lit 1) = a.testBit k := by
    rw [e, Nat.testBit_eq_decide_div_mod_eq]
    exact Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])
  have hs : ∀ (y : Nat) (q : Nat → Nat), strictN y q = q y := fun y q => by cases y <;> rfl
  change strictN (fxR P a k) (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1))
    (nat_lit 1), Nat.xor s (colK P k), s)) = _
  rw [hs]
  change Bool.rec (motive := fun _ => Nat) _ _
    (Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1)) (nat_lit 1)) = _
  rw [hb]
  cases a.testBit k <;> rfl

theorem fx_xor (P a b : Nat) : appK P (a ^^^ b) = appK P a ^^^ appK P b := by
  suffices h : ∀ k, fxR P (a ^^^ b) k = fxR P a k ^^^ fxR P b k from h 11
  intro k
  induction k with
  | zero =>
    change (0 : Nat) = 0 ^^^ 0
    rw [Nat.xor_self]
  | succ k ih =>
    rw [fxR_succ, fxR_succ, fxR_succ, ih, Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> simp only [Bool.true_xor, Bool.false_xor,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor] <;>
      cases (fxR P a k).testBit i <;> cases (fxR P b k).testBit i <;>
      cases (colK P k).testBit i <;> rfl

theorem fx_zero (P : Nat) : appK P 0 = 0 := by
  have h := fx_xor P 0 0
  rwa [Nat.xor_self, Nat.xor_self] at h

theorem fx_lt {G d a : Nat} (h : ∀ j < 11, colK G j < 2 ^ d) : appK G a < 2 ^ d := by
  suffices h' : ∀ k ≤ 11, fxR G a k < 2 ^ d from h' 11 (Nat.le_refl 11)
  intro k
  induction k with
  | zero =>
    intro _
    exact Nat.two_pow_pos d
  | succ k ih =>
    intro hk
    rw [fxR_succ]
    split
    · exact Nat.xor_lt_two_pow (ih (by omega)) (h k (by omega))
    · exact ih (by omega)

theorem fx_split (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 ^ k ^^^ (if n.testBit k then 2 ^ k else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · rw [Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i k with hi | hi | hi
    · simp [hi, Nat.ne_of_gt hi, show i < k + 1 by omega]
    · subst hi
      simp_all
    · simp [show ¬ i < k by omega, show ¬ i < k + 1 by omega, Nat.ne_of_lt hi]
  · rw [Nat.zero_testBit, Bool.xor_false]
    rcases Nat.lt_trichotomy i k with hi | hi | hi
    · simp [hi, show i < k + 1 by omega]
    · subst hi
      simp_all
    · simp [show ¬ i < k by omega, show ¬ i < k + 1 by omega]

theorem fx_ext {f g : Nat → Nat} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) (hu : ∀ i < 11, f (2 ^ i) = g (2 ^ i)) :
    ∀ n < 2048, f n = g n := by
  have h0 : ∀ φ : Nat → Nat, (∀ a b, φ (a ^^^ b) = φ a ^^^ φ b) → φ 0 = 0 := fun φ hφ => by
    have h := hφ 0 0
    rwa [Nat.xor_self, Nat.xor_self] at h
  suffices h : ∀ k ≤ 11, ∀ n, f (n % 2 ^ k) = g (n % 2 ^ k) by
    intro n hn
    have h' := h 11 (Nat.le_refl 11) n
    rwa [Nat.mod_eq_of_lt (by omega)] at h'
  intro k
  induction k with
  | zero =>
    intro _ n
    rw [Nat.pow_zero, Nat.mod_one, h0 f hf, h0 g hg]
  | succ k ih =>
    intro hk n
    rw [fx_split, hf, hg, ih (by omega)]
    split
    · rw [hu k (by omega)]
    · rw [h0 f hf, h0 g hg]

theorem idx_ok {e n : Nat} (he : e < 1024) (hn : n < 2048)
    (h : squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧ ¬ (n = 0 ∧ e = 0)) :
    forestIdx[n + 2048 * e]! - 1 < 19967 ∧ fN (forestIdx[n + 2048 * e]! - 1) = n ∧
      fE (forestIdx[n + 2048 * e]! - 1) = e := by
  have hx : J4InvC.idxK e = true := slice_spec (k := 64) (S := 16) (by omega) J4IX.all e (by omega)
  have hfix := (fix_iff he).2 h
  unfold J4InvC.idxK at hx
  have hsq : Nat.beq (J4SQ.T e) 0 = true := by
    rw [beq_iff, ← SQ_get he]
    exact h.1
  have hsl : ∀ d : Nat, Nat.shiftLeft 1 d = 2 ^ d := fun d => Nat.one_shiftLeft d
  rw [bIf_t ((bAnd_iff _ _).2 ⟨blt_iff.2 he, hsq⟩), strictB_eq, strictB_eq] at hx
  generalize J4FX e = X at hx
  obtain ⟨hc, hall⟩ := (bAnd_iff _ _).1 hx
  unfold fxK at hc
  obtain ⟨hG, hU⟩ := (bAnd_iff _ _).1 hc
  have hG' : ∀ j < 11, colK (ent 121 X 1) j < 2 ^ ent 121 X 3 := fun j hj => by
    have hj' := allN_spec hG j hj
    rw [hsl] at hj'
    exact blt_iff.1 hj'
  have hPn : appK (J4E.T e) n = n := by
    have h2 := h.2.1
    rwa [J4Five.E_eq he, app_eq] at h2
  have hlin := fx_ext (f := fun m => m ^^^ appK (ent 121 X 0) (appK (ent 121 X 1) m))
    (g := fun m => appK (ent 121 X 2) (appK (J4E.T e) m ^^^ m))
    (fun a b => by
      simp only [fx_xor]
      ac_rfl)
    (fun a b => by
      simp only [fx_xor]
      ac_rfl)
    (fun i hi => by
      have hi' := beq_iff.1 (allN_spec hU i hi)
      rw [hsl] at hi'
      exact hi') n hn
  simp only [hPn, Nat.xor_self, fx_zero] at hlin
  have hn' := congrArg (· ^^^ appK (ent 121 X 0) (appK (ent 121 X 1) n)) hlin
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at hn'
  have hw := allN_spec hall (appK (ent 121 X 1) n) (by
    rw [hsl]
    exact fx_lt hG')
  rw [strictB_eq, ← hn'] at hw
  unfold idxRK at hw
  have hfix' : idxFixK (J4E.T e) n e = true := ((bAnd_iff _ _).1 hfix).2
  rw [bIf_t hfix'] at hw
  obtain ⟨w1, hw⟩ := (bAnd_iff _ _).1 hw
  obtain ⟨w2, w3⟩ := (bAnd_iff _ _).1 hw
  have hj := blt_iff.1 w1
  have hk : key (WI n e) = n + 2048 * e := by
    rw [key, fN_eq hj, fE_eq hj, beq_iff.1 w2, beq_iff.1 w3]
  obtain ⟨_, hi, hne⟩ := fold_inv 19967 le_rfl
  rw [fidx_fold]
  have hne' := hne (WI n e) hj
  rw [hk] at hne'
  rcases hi (n + 2048 * e) (by omega) with h0 | ⟨j, hj', h1, h2⟩
  · exact absurd h0 hne'
  · rw [h1, Nat.add_sub_cancel]
    have hr := (rec_ok hj').1
    unfold key at h2
    refine ⟨hj', ?_, ?_⟩ <;> omega

theorem sufN_ok {w : List Int} {T : List Nat} {N : Nat} (hseg : ∀ k < N, segN w T N k = true)
    (hb : getN one T N = one ∧ getN one T (N + 1 + N) = one) (hlen : w.length ≤ 100 * N)
    (hlet : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    ∀ m ≤ N, PairOK (wordP Xn Yn (w.drop (100 * (N - m)))) (getN one T (N - m))
      (getN one T (N + 1 + (N - m)))
  | 0, _ => by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by omega), hb.1, hb.2]
    exact oneP_ok J4Real.hK
  | m + 1, hm => by
    have ih := sufN_ok hseg hb hlen hlet m (by omega)
    have h := hseg (N - (m + 1)) (by omega)
    unfold segN at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [dropI_eq, takeI_eq] at h1 h2
    have e1 : Nat.succ (N - (m + 1)) = N - m := by omega
    have e2 : Nat.add (Nat.add N 2) (N - (m + 1)) = N + 1 + (N - m) := by
      change N + 2 + (N - (m + 1)) = N + 1 + (N - m)
      omega
    have e3 : Nat.add (Nat.succ N) (N - (m + 1)) = N + 1 + (N - (m + 1)) := rfl
    have e4 : Nat.mul 100 (N - (m + 1)) = 100 * (N - (m + 1)) := rfl
    rw [e1, e4] at h1
    rw [e2, e3, e4] at h2
    have split : w.drop (100 * (N - (m + 1))) =
        (w.drop (100 * (N - (m + 1)))).take 100 ++ w.drop (100 * (N - m)) := by
      conv_lhs => rw [← List.take_append_drop 100 (w.drop (100 * (N - (m + 1))))]
      rw [List.drop_drop, show 100 * (N - (m + 1)) + 100 = 100 * (N - m) by omega]
    have := wordP_ok J4Real.hK pX pY ih ((w.drop (100 * (N - (m + 1)))).take 100)
      (fun l hl => hlet l (List.mem_of_mem_drop (List.mem_of_mem_take hl)))
    rw [← split, beq_iff.1 h1, beq_iff.1 h2] at this
    exact this

theorem word_ok {w : List Int} {T : List Nat} {N : Nat} (hseg : ∀ s < N, allBlk (Nat.mul 1 s)
    (fun k => segN w T N k) 1 = true)
    (hb : bAnd(Nat.beq (getN one T N) one, Nat.beq (getN one T (N + 1 + N)) one) = true)
    (hlen : w.length ≤ 100 * N) (hlet : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    PairOK (wordP Xn Yn w) (getN one T 0) (getN one T (N + 1)) := by
  obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 hb
  have := sufN_ok (fun k hk => slice_spec (k := 1) (by omega) hseg k (by omega))
    ⟨beq_iff.1 b1, beq_iff.1 b2⟩ hlen hlet N le_rfl
  rwa [Nat.sub_self, Nat.mul_zero, List.drop_zero, Nat.add_zero] at this

theorem lettersW {w : List Int} (hw : w ∈ J4FW.ws) : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 :=
  letters w hw

private theorem pairOK_congr {P : Pair} {a b a' b' : Nat} (h : PairOK P a b) (ha : a = a')
    (hb : b = b') : PairOK P a' b' := by
  rw [← ha, ← hb]
  exact h

private theorem getN_list8 (d a0 a1 a2 a3 a4 a5 a6 a7 : Nat) :
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 0 = a0 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 1 = a1 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 2 = a2 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 3 = a3 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 4 = a4 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 5 = a5 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 6 = a6 ∧
    getN d [a0, a1, a2, a3, a4, a5, a6, a7] 7 = a7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem KL_eq : KL = [getN one J4K0 0, getN one J4K1 0, getN one J4K2 0, getN one J4K3 0,
    getN one J4K0 170, getN one J4K1 59, getN one J4K2 3, getN one J4K3 4] := by
  rw [KL]

private theorem ws_get0 : J4FW.ws.toArray[0]! = J4FW.w0 := rfl

private theorem ws_get1 : J4FW.ws.toArray[1]! = J4FW.w1 := rfl

private theorem ws_get2 : J4FW.ws.toArray[2]! = J4FW.w2 := rfl

private theorem ws_get3 : J4FW.ws.toArray[3]! = J4FW.w3 := rfl

private theorem arr4_get {α : Type} [Inhabited α] (a b c d : α) :
    #[a, b, c, d][0]! = a ∧ #[a, b, c, d][1]! = b ∧ #[a, b, c, d][2]! = c ∧
      #[a, b, c, d][3]! = d :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem kpair0 : KPairs[0]! = wordP Xn Yn J4FW.w0 := by
  rw [KPairs, (arr4_get _ _ _ _).1, J4Five.fw_eq, ws_get0]

private theorem mem0 : J4FW.w0 ∈ J4FW.ws := by simp [J4FW.ws]

private theorem hseg0 : ∀ s < 169,
    allBlk (Nat.mul 1 s) (fun k => segN J4FW.w0 J4K0 169 k) 1 = true :=
  J4KS0.all

private theorem hb0 : bAnd(Nat.beq (getN one J4K0 169) one,
    Nat.beq (getN one J4K0 (169 + 1 + 169)) one) = true :=
  b0

private theorem word0 :
    PairOK (wordP Xn Yn J4FW.w0) (getN one J4K0 0) (getN one J4K0 (169 + 1)) :=
  word_ok hseg0 hb0 len0 (lettersW mem0)

private theorem kp0_ok :
    PairOK KPairs[0]! (getN one KL 0) (getN one KL (Nat.add 4 0)) := by
  rw [kpair0]
  refine pairOK_congr word0 ?_ ?_
  · rw [KL_eq]
    exact (getN_list8 one _ _ _ _ _ _ _ _).1.symm
  · rw [KL_eq, show Nat.add 4 0 = 4 from rfl, show (169 : Nat) + 1 = 170 from rfl]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.2.2.1.symm

private theorem kpair1 : KPairs[1]! = wordP Xn Yn J4FW.w1 := by
  rw [KPairs, (arr4_get _ _ _ _).2.1, J4Five.fw_eq, ws_get1]

private theorem mem1 : J4FW.w1 ∈ J4FW.ws := by simp [J4FW.ws]

private theorem hseg1 : ∀ s < 58,
    allBlk (Nat.mul 1 s) (fun k => segN J4FW.w1 J4K1 58 k) 1 = true :=
  J4KS1.all

private theorem hb1 : bAnd(Nat.beq (getN one J4K1 58) one,
    Nat.beq (getN one J4K1 (58 + 1 + 58)) one) = true :=
  b1

private theorem word1 :
    PairOK (wordP Xn Yn J4FW.w1) (getN one J4K1 0) (getN one J4K1 (58 + 1)) :=
  word_ok hseg1 hb1 len1 (lettersW mem1)

private theorem kp1_ok :
    PairOK KPairs[1]! (getN one KL 1) (getN one KL (Nat.add 4 1)) := by
  rw [kpair1]
  refine pairOK_congr word1 ?_ ?_
  · rw [KL_eq]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.1.symm
  · rw [KL_eq, show Nat.add 4 1 = 5 from rfl, show (58 : Nat) + 1 = 59 from rfl]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.2.2.2.1.symm

private theorem kpair2 : KPairs[2]! = wordP Xn Yn J4FW.w2 := by
  rw [KPairs, (arr4_get _ _ _ _).2.2.1, J4Five.fw_eq, ws_get2]

private theorem mem2 : J4FW.w2 ∈ J4FW.ws := by simp [J4FW.ws]

private theorem hseg2 : ∀ s < 2,
    allBlk (Nat.mul 1 s) (fun k => segN J4FW.w2 J4K2 2 k) 1 = true :=
  J4KS2.all

private theorem hb2 : bAnd(Nat.beq (getN one J4K2 2) one,
    Nat.beq (getN one J4K2 (2 + 1 + 2)) one) = true :=
  b2

private theorem word2 :
    PairOK (wordP Xn Yn J4FW.w2) (getN one J4K2 0) (getN one J4K2 (2 + 1)) :=
  word_ok hseg2 hb2 len2 (lettersW mem2)

private theorem kp2_ok :
    PairOK KPairs[2]! (getN one KL 2) (getN one KL (Nat.add 4 2)) := by
  rw [kpair2]
  refine pairOK_congr word2 ?_ ?_
  · rw [KL_eq]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.1.symm
  · rw [KL_eq, show Nat.add 4 2 = 6 from rfl, show (2 : Nat) + 1 = 3 from rfl]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.2.2.2.2.1.symm

private theorem kpair3 : KPairs[3]! = wordP Xn Yn J4FW.w3 := by
  rw [KPairs, (arr4_get _ _ _ _).2.2.2, J4Five.fw_eq, ws_get3]

private theorem mem3 : J4FW.w3 ∈ J4FW.ws := by simp [J4FW.ws]

private theorem hseg3 : ∀ s < 3,
    allBlk (Nat.mul 1 s) (fun k => segN J4FW.w3 J4K3 3 k) 1 = true :=
  J4KS3.all

private theorem hb3 : bAnd(Nat.beq (getN one J4K3 3) one,
    Nat.beq (getN one J4K3 (3 + 1 + 3)) one) = true :=
  b3

private theorem word3 :
    PairOK (wordP Xn Yn J4FW.w3) (getN one J4K3 0) (getN one J4K3 (3 + 1)) :=
  word_ok hseg3 hb3 len3 (lettersW mem3)

private theorem kp3_ok :
    PairOK KPairs[3]! (getN one KL 3) (getN one KL (Nat.add 4 3)) := by
  rw [kpair3]
  refine pairOK_congr word3 ?_ ?_
  · rw [KL_eq]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.2.1.symm
  · rw [KL_eq, show Nat.add 4 3 = 7 from rfl, show (3 : Nat) + 1 = 4 from rfl]
    exact (getN_list8 one _ _ _ _ _ _ _ _).2.2.2.2.2.2.2.symm

theorem kp_ok {g : Nat} (hg : g < 4) :
    PairOK KPairs[g]! (getN one KL g) (getN one KL (Nat.add 4 g)) := by
  obtain rfl | rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
  · exact kp0_ok
  · exact kp1_ok
  · exact kp2_ok
  · exact kp3_ok

theorem u_ok : ∀ (f e : Nat), e < f → e < 1024 →
    PairOK (uPairK KPairs e) (uF f e) (uS f e)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, e, hf, he => by
    rw [uPairK]
    have g0 : (discoveryParents[e]!)[0]! = p0 e := J4Five.D_get he (by omega)
    have g1 : (discoveryParents[e]!)[1]! = p1 e := J4Five.D_get he (by omega)
    rw [g0, g1]
    have eF : uF (f + 1) e = nIf(bAnd(Nat.blt 0 e, Nat.blt (p0 e) e),
        CFSG.KC.Loop.strictN (uF f (p0 e)) fun u => mulJ c rm u (getN one KL (p1 e)), one) := rfl
    have eS : uS (f + 1) e = nIf(bAnd(Nat.blt 0 e, Nat.blt (p0 e) e),
        CFSG.KC.Loop.strictN (uS f (p0 e)) fun u => mulJ c rm (getN one KL (Nat.add 4 (p1 e))) u,
        one) := rfl
    rw [eF, eS]
    by_cases hc : 0 < e ∧ p0 e < e
    · have hb : bAnd(Nat.blt 0 e, Nat.blt (p0 e) e) = true :=
        (bAnd_iff _ _).2 ⟨blt_iff.2 hc.1, blt_iff.2 hc.2⟩
      rw [dite_eq_left hc, nIf_t hb, nIf_t hb, strictN_eq', strictN_eq']
      have hp := allN_spec par e he
      change bIf(bAnd(Nat.blt 0 e, Nat.blt (p0 e) e), Nat.blt (p1 e) 4, true) = true at hp
      rw [bIf_t hb] at hp
      exact mulP_ok J4Real.hK (u_ok f (p0 e) (by omega) (by omega)) (kp_ok (blt_iff.1 hp))
    · have hb : bAnd(Nat.blt 0 e, Nat.blt (p0 e) e) = false := by
        cases h : bAnd(Nat.blt 0 e, Nat.blt (p0 e) e)
        · rfl
        · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
          exact absurd ⟨blt_iff.1 h1, blt_iff.1 h2⟩ hc
      rw [dite_eq_right hc, nIf_f hb, nIf_f hb]
      exact oneP_ok J4Real.hK

theorem pA : PairOK An A A := ⟨J4Real.hA, J4Real.hA⟩
theorem pB : PairOK Bn B Bi := ⟨J4Real.hB, J4Real.hB3⟩

theorem hExp_lt : hExp < 2 ^ 45 := by
  rw [hExp]
  norm_num

theorem amb_ok {i : Nat} (hi : i < 77) : ambCheck KPairs i = true := by
  have hr : rootK i = true := by
    have := allBlk_spec (J4IA.all i hi) 0 Nat.zero_lt_one
    rwa [show Nat.add (Nat.mul 1 i) 0 = i by simp] at this
  have ha := allN_spec ah i hi
  obtain ⟨_, ha⟩ := (bAnd_iff _ _).1 ha
  obtain ⟨ha1, ha2⟩ := (bAnd_iff _ _).1 ha
  unfold rootK ambB at hr
  simp only [strictB_eq] at hr
  obtain ⟨hr1, hr2⟩ := (bAnd_iff _ _).1 hr
  have hw : ∀ l ∈ ambWords[i]!, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
    rw [aw_get, ← getW_eq]
    intro l hl
    rcases h : J4AW.ws[i]? with _ | w
    · rw [h] at hl
      simp at hl
    · rw [h, Option.getD_some] at hl
      exact lettersA w (List.mem_of_getElem? h) l hl
  have pw := wordP_ok' J4Real.hK pA pB _ hw
  rw [aw_get] at pw
  have pn := etaP_ok (AH 0 i)
  have ps := etaP_ok (AH 2 i)
  have pu := u_ok 1024 (AH 1 i) (blt_iff.1 ha1) (blt_iff.1 ha1)
  have pa := mulP_ok J4Real.hK pn pu
  have pt := mulP_ok J4Real.hK (mulP_ok J4Real.hK pw ps) (invP_ok pw)
  have ph := mulP_ok J4Real.hK pa pt
  have pp := powBP_ok J4Real.hK ph 45 hExp hExp_lt
  have pc := mulP_ok J4Real.hK (invP_ok pw) pp
  have pf := mulP_ok J4Real.hK (mulP_ok J4Real.hK pc pa) (invP_ok pc)
  simp only [ambCheck, ambConj]
  rw [A_get hi (k := 0) (by omega), A_get hi (k := 1) (by omega), A_get hi (k := 2) (by omega),
    aw_get, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have e1 : ∀ X Y : Array Nat, O.eq X Y = (X == Y) := fun _ _ => rfl
    rw [e1, beq_enc pf.1.1 ps.1.1, pf.1.2, ps.1.2]
    exact hr1
  · by_cases h1 : AH 2 i = 1
    · rw [h1]
      rfl
    · rw [bIf_f (beqF h1), beq_iff] at hr2
      rw [hr2]
      rfl

theorem facts : (∀ i < 4, comp11 generatorColumns[i]! genInvColumns[i]! = idRows 11)
    ∧ (∀ i < 4, ∀ e < 1024, (conjTab[i]!)[e]! < 1024 ∧
      elementColumns[(conjTab[i]!)[e]!]! =
        comp11 (comp11 generatorColumns[i]! elementColumns[e]!) genInvColumns[i]!)
    ∧ (∀ j < 19967, (fN j < 2048 ∧ fE j < 1024 ∧ squares[fE j]! = 0 ∧
      app11 elementColumns[fE j]! (fN j) = fN j ∧ ¬ (fN j = 0 ∧ fE j = 0)) ∧
      ((fP j = j ∧ (fE j = 0 ∨ ambIdx (fN j) (fE j) < 77)) ∨
        (fP j < j ∧ fG j < 5 ∧ genMapN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧
          genMapE (fG j) (fE (fP j)) = fE j)))
    ∧ (∀ e < 1024, ∀ n < 2048,
      (squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧ ¬ (n = 0 ∧ e = 0)) →
        (forestIdx[n + 2048 * e]! - 1 < 19967 ∧ fN (forestIdx[n + 2048 * e]! - 1) = n ∧
          fE (forestIdx[n + 2048 * e]! - 1) = e))
    ∧ (∀ i < 77, (ambHead[i]!)[0]! < 2048 ∧ (ambHead[i]!)[1]! < 1024)
    ∧ (ambAllOK KPairs = true) := by
  refine ⟨fun i hi => ?_, fun i hi e he => ?_, fun j hj => rec_ok hj,
    fun e he n hn h => idx_ok he hn h, fun i hi => ?_, ?_⟩
  · rw [J4Five.GC_eq hi, GI_eq hi, comp_eq, CFSG.KS.SporSch.C11.id_eq, beq_iff.1 (allN_spec gi i hi)]
  · have hc : allN 1024 (conjK i) = true := by
      obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      exacts [conj0, conj1, conj2, conj3]
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hc e he)
    have l1 := blt_iff.1 h1
    rw [C_get hi he]
    refine ⟨l1, ?_⟩
    rw [J4Five.E_eq l1, J4Five.E_eq he, J4Five.GC_eq hi, GI_eq hi, comp_eq, comp_eq,
      beq_iff.1 h2]
  · obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 (allN_spec ah i hi)
    obtain ⟨h2, _⟩ := (bAnd_iff _ _).1 h
    rw [A_get hi (by omega), A_get hi (by omega)]
    exact ⟨blt_iff.1 h1, blt_iff.1 h2⟩
  · rw [ambAllOK, List.all_eq_true]
    intro i hi
    exact amb_ok (List.mem_range.1 hi)

end CertificateChecks.KernelSporSch.J4InvP

end
