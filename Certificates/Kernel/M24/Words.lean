module

public import CFSG.Certificates.Kernel.M24RsSound
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.KM24.Words

open CFSG.KM24 CFSG.Certificates

theorem land_65535 (x : ℕ) : Nat.land x 65535 = x % 65536 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 16
  norm_num at h
  exact h

theorem land_255 (x : ℕ) : Nat.land x 255 = x % 256 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 8
  norm_num at h
  exact h

theorem lt_eq (w i : ℕ) : lt w i = w / 2 ^ (16 * i) % 65536 := by
  change Nat.land (w >>> (16 * i)) 65535 = _
  rw [land_65535, Nat.shiftRight_eq_div_pow]

theorem wLet_eq (w i : ℕ) : CFSG.KC.wLet w i = w / 2 ^ (8 * i) % 256 := by
  change Nat.land (w >>> (8 * i)) 255 = _
  rw [land_255, Nat.shiftRight_eq_div_pow]

theorem lor_shift (c v k : ℕ) (hc : c < 2 ^ k) : Nat.lor c (Nat.shiftLeft v k) = v * 2 ^ k + c := by
  change c ||| v <<< k = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hc, Nat.shiftLeft_eq]

theorem digit_low (x d b m j : ℕ) (hx : x < 2 ^ (b * m)) (hj : j < m) :
    (d * 2 ^ (b * m) + x) / 2 ^ (b * j) % 2 ^ b = x / 2 ^ (b * j) % 2 ^ b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = j + 1 + k := ⟨m - j - 1, by omega⟩
  have e : d * 2 ^ (b * (j + 1 + k)) = (d * 2 ^ (b * (1 + k))) * 2 ^ (b * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    ring
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mod]
  have : d * 2 ^ (b * (1 + k)) % 2 ^ b = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by nlinarith)) d
  rw [this, Nat.add_zero, Nat.mod_mod]

theorem digit_top (x d b m : ℕ) (hx : x < 2 ^ (b * m)) (hd : d < 2 ^ b) :
    (d * 2 ^ (b * m) + x) / 2 ^ (b * m) % 2 ^ b = d := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, Nat.zero_add, Nat.mod_eq_of_lt hd]

noncomputable def byteFold (d : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor acc (Nat.shiftLeft (d j) (Nat.mul 8 j))) m

theorem byteFold_succ (d : ℕ → ℕ) (m : ℕ) (hF : byteFold d m < 2 ^ (8 * m)) :
    byteFold d (m + 1) = d m * 2 ^ (8 * m) + byteFold d m := by
  change Nat.lor (byteFold d m) (Nat.shiftLeft (d m) (8 * m)) = _
  rw [lor_shift _ _ _ hF]

theorem byteFold_spec (d : ℕ → ℕ) (M : ℕ) (hd : ∀ j < M, d j < 2 ^ 8) :
    ∀ m ≤ M, byteFold d m < 2 ^ (8 * m) ∧ ∀ j < m, byteFold d m / 2 ^ (8 * j) % 256 = d j := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨by simp [byteFold], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    intro hm
    obtain ⟨hF, hj⟩ := ih (by omega)
    have hdm := hd m (by omega)
    rw [byteFold_succ d m hF]
    refine ⟨?_, fun j hjm => ?_⟩
    · calc d m * 2 ^ (8 * m) + byteFold d m < d m * 2 ^ (8 * m) + 2 ^ (8 * m) := by omega
        _ = (d m + 1) * 2 ^ (8 * m) := by ring
        _ ≤ 2 ^ 8 * 2 ^ (8 * m) := Nat.mul_le_mul_right _ hdm
        _ = 2 ^ (8 * (m + 1)) := by rw [← Nat.pow_add]; ring_nf
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with h | h
      · have := digit_low (byteFold d m) (d m) 8 m j hF h
        rw [show (2 : ℕ) ^ 8 = 256 by norm_num] at this
        rw [this, hj j h]
      · subst h
        have := digit_top (byteFold d j) (d j) 8 j hF hdm
        rwa [show (2 : ℕ) ^ 8 = 256 by norm_num] at this

theorem eqRL_eq : ∀ (A B : List ℕ), eqRL A B = true → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqRL])
  | _ :: _, [], h => absurd h (by simp [eqRL])
  | a :: A, b :: B, h => by
    change mAnd (Nat.beq a b) (eqRL A B) = true at h
    cases hab : Nat.beq a b
    · rw [hab] at h
      exact absurd h (by simp [mAnd])
    · rw [hab] at h
      rw [Nat.beq_eq] at hab
      rw [hab, eqRL_eq A B h]

theorem getR_mem : ∀ (L : List ℕ) (i : ℕ), i < L.length → getR L i ∈ L
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: L, 0, _ => List.mem_cons_self
  | x :: L, i + 1, h => List.mem_cons_of_mem _ (getR_mem L i (by simpa using h))

theorem lenR_eq : ∀ L : List ℕ, lenR L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenR L) = _
    rw [lenR_eq L]
    rfl

theorem mAnd_eq_true {a b : Bool} (h : mAnd a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp [mAnd])
  · exact ⟨rfl, h⟩

theorem loopL (f : ℕ → Bool) :
    ∀ m, Nat.rec (motive := fun _ => Bool) true (fun j acc => mAnd acc (f j)) m = true →
      ∀ j < m, f j = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, h, j, hj => by
    obtain ⟨h1, h2⟩ := mAnd_eq_true h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact loopL f m h1 j hj
    · exact h2

theorem loopR (f : ℕ → Bool) :
    ∀ m, Nat.rec (motive := fun _ => Bool) true (fun j acc => mAnd (f j) acc) m = true →
      ∀ j < m, f j = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, h, j, hj => by
    obtain ⟨h1, h2⟩ := mAnd_eq_true h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact loopR f m h2 j hj
    · exact h1

theorem rsOk_intro {T P k2 nc : ℕ} {R0 A0 : List ℕ} {G0 : ℕ}
    {steps : List (ℕ × (ℕ × (List ℕ × ℕ)))} {N : ℕ} {Rn : List ℕ} {ng kq : ℕ}
    (h1 : mAnd (Nat.beq (Nat.mod k2 (nat_lit 2)) (nat_lit 0)) (mAnd (Nat.blt (nat_lit 0) nc)
      (mAnd (Nat.blt (Nat.mul nc k2) (nat_lit 32768)) (lettersLt R0 k2))) = true)
    (h2 : chkInit T P k2 nc R0 A0 G0 = true) (h3 : rsChain A0 G0 steps N Rn ng kq = true) :
    rsOk T P k2 nc R0 A0 G0 steps N Rn ng kq = true := by
  obtain ⟨a, r⟩ := mAnd_eq_true h1
  obtain ⟨b, r⟩ := mAnd_eq_true r
  obtain ⟨c, d⟩ := mAnd_eq_true r
  simp only [rsOk, a, b, c, d, h2, h3]
  rfl

theorem rsChain_cons {A A' : List ℕ} {GA G' B m : ℕ} {rest : List (ℕ × (ℕ × (List ℕ × ℕ)))}
    {N : ℕ} {Rn : List ℕ} {ng kq : ℕ} (h : chkReplayG B m A A' GA G' = true)
    (h' : rsChain A' G' rest N Rn ng kq = true) :
    rsChain A GA ((B, m, A', G') :: rest) N Rn ng kq = true := by
  change mAnd (chkReplayG B m A A' GA G') (rsChain A' G' rest N Rn ng kq) = true
  rw [h, h']
  rfl

theorem rsChain_nil {A : List ℕ} {GA N : ℕ} {Rn : List ℕ} {ng kq : ℕ}
    (h : chkNext N A Rn GA ng kq = true) : rsChain A GA [] N Rn ng kq = true := h

theorem pk_eq (v n : ℕ) (hn : n < 65536) : pk v n = v * 65536 + n :=
  lor_shift n v 16 (by simpa using hn)

theorem pn_pk (v n : ℕ) (hn : n < 65536) : pn (pk v n) = n := by
  change Nat.land (pk v n) 65535 = n
  rw [land_65535, pk_eq v n hn, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hn]

theorem pw_pk (v n : ℕ) (hn : n < 65536) : pw (pk v n) = v := by
  change pk v n >>> 16 = v
  rw [Nat.shiftRight_eq_div_pow, pk_eq v n hn, Nat.add_comm, show (2 : ℕ) ^ 16 = 65536 by norm_num,
    Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt hn, Nat.zero_add]

theorem lt_cons0 (c v : ℕ) (hc : c < 65536) : lt (Nat.lor c (Nat.shiftLeft v 16)) 0 = c := by
  rw [lor_shift c v 16 (by simpa using hc), lt_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
    show (2 : ℕ) ^ 16 = 65536 by norm_num, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc]

theorem lt_consS (c v i : ℕ) (hc : c < 65536) :
    lt (Nat.lor c (Nat.shiftLeft v 16)) (i + 1) = lt v i := by
  have e : (v * 2 ^ 16 + c) / 2 ^ 16 = v := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by simpa using hc), Nat.zero_add]
  rw [lor_shift c v 16 (by simpa using hc), lt_eq, lt_eq, show 16 * (i + 1) = 16 + 16 * i by ring,
    Nat.pow_add, ← Nat.div_div_eq_div_mul, e]

noncomputable def qval {G : Type*} [Group G] (gen : ℕ → G) (v n : ℕ) : G :=
  ((List.range n).map fun i => letP gen (lt v i)).prod

theorem qval_cons {G : Type*} [Group G] (gen : ℕ → G) (c v n : ℕ) (hc : c < 65536) :
    qval gen (Nat.lor c (Nat.shiftLeft v 16)) (n + 1) = letP gen c * qval gen v n := by
  rw [qval, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, lt_cons0 c v hc]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, lt_consS c v i hc]

theorem letP_letCode {G : Type*} [Group G] (gen : ℕ → G) (x : ℕ × Bool) :
    letP gen (CFSG.KBAlt.M24.letCode x) = if x.2 then gen x.1 else (gen x.1)⁻¹ := by
  obtain ⟨g, b⟩ := x
  cases b
  · change letP gen (2 * g + 1) = _
    simp [letP, Nat.add_mod, Nat.add_div]
  · change letP gen (2 * g) = _
    simp [letP]

theorem letCode_lt (x : ℕ × Bool) (h : x.1 < 32768) : CFSG.KBAlt.M24.letCode x < 65536 := by
  obtain ⟨g, b⟩ := x
  cases b
  · change 2 * g + 1 < 65536
    simp only at h
    omega
  · change 2 * g < 65536
    simp only at h
    omega

theorem encW_val {G : Type*} [Group G] (gen : ℕ → G) :
    ∀ w : List (ℕ × Bool), (∀ x ∈ w, x.1 < 32768) →
      (CFSG.KBAlt.M24.encW w).2 = w.length ∧
        qval gen (CFSG.KBAlt.M24.encW w).1 (CFSG.KBAlt.M24.encW w).2 = KB.sword gen w
  | [], _ => ⟨rfl, rfl⟩
  | x :: w, h => by
    obtain ⟨h1, h2⟩ := encW_val gen w fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := letCode_lt x (h x List.mem_cons_self)
    change (CFSG.KBAlt.M24.encW w).2 + 1 = w.length + 1 ∧
      qval gen (Nat.lor (CFSG.KBAlt.M24.letCode x) (Nat.shiftLeft (CFSG.KBAlt.M24.encW w).1 16))
        ((CFSG.KBAlt.M24.encW w).2 + 1) = KB.sword gen (x :: w)
    refine ⟨by rw [h1], ?_⟩
    rw [qval_cons _ _ _ _ hx, h2, letP_letCode, KB.sword, KB.sword, List.map_cons, List.prod_cons]

theorem pval_encRel {G : Type*} [Group G] (gen : ℕ → G) (w : List (ℕ × Bool))
    (h : ∀ x ∈ w, x.1 < 32768) (hl : w.length < 65536) :
    pval gen (CFSG.KBAlt.M24.encRel w) = KB.sword gen w := by
  obtain ⟨h1, h2⟩ := encW_val gen w h
  change pval gen (pk (CFSG.KBAlt.M24.encW w).1 (CFSG.KBAlt.M24.encW w).2) = _
  rw [h1] at h2 ⊢
  rw [pval, pn_pk _ _ hl, pw_pk _ _ hl]
  exact h2

theorem encRels_eq : ∀ L : List (List (ℕ × Bool)),
    CFSG.KBAlt.M24.encRels L = L.map CFSG.KBAlt.M24.encRel
  | [] => rfl
  | w :: L => by
    change CFSG.KBAlt.M24.encRel w :: CFSG.KBAlt.M24.encRels L = _
    rw [encRels_eq L, List.map_cons]

theorem letV_eq_letP {G : Type*} [Group G] (gen : ℕ → G) (l : ℕ) (hl : l ≠ 255) :
    LCE.letV gen l = letP gen l := by
  simp [LCE.letV, letP, hl]

theorem bval_chkByteRel {G : Type*} [Group G] (gen : ℕ → G) {L : List ℕ} {i m k2 v : ℕ}
    (hk : k2 ≤ 255) (h : chkByteRel L i m k2 v = true) : LCE.bval gen v m = pval gen (getR L i) := by
  obtain ⟨hn, h⟩ := mAnd_eq_true h
  obtain ⟨hlt, hv⟩ := mAnd_eq_true h
  rw [Nat.beq_eq] at hn hv
  have hall : ∀ j < m, lt (pw (getR L i)) j < k2 := fun j hj =>
    Nat.blt_eq.mp (loopL (fun j => Nat.blt (lt (pw (getR L i)) j) k2) m hlt j hj)
  have hv' : v = byteFold (lt (pw (getR L i))) m := hv
  have hspec := byteFold_spec (lt (pw (getR L i))) m (fun j hj => by
    have := hall j hj
    norm_num
    omega) m le_rfl
  rw [LCE.bval, pval, hn]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  have hj' := hall j hj
  rw [wLet_eq, hv', hspec.2 j hj, letV_eq_letP _ _ (by omega)]

theorem bval_rtBind {G : Type*} [Group G] (gen : ℕ → G) {RT : ℕ → ℕ} {Rn : List ℕ} {nR k2 : ℕ}
    (hk : k2 ≤ 255) (h : rtBind RT Rn nR k2 = true) :
    ∀ r < nR, LCE.bval gen (CFSG.KC.LceS.wWord (RT r)) (CFSG.KC.LceS.wLen (RT r)) =
      pval gen (getR Rn r) := fun r hr =>
  bval_chkByteRel gen hk (loopR (fun r => chkByteRel Rn r
    (Nat.land (Nat.shiftRight (RT r) 2) 1023) k2 (Nat.shiftRight (RT r) 12)) nR h r hr)

theorem bval_allLet {G : Type*} [Group G] (gen : ℕ → G) {W n c : ℕ} (h : allLet W n c = true) :
    LCE.bval gen W n = LCE.letV gen c ^ n := by
  have hall : ∀ i < n, CFSG.KC.wLet W i = c := fun i hi => Nat.beq_eq.mp
    (loopR (fun i => Nat.beq (Nat.land (Nat.shiftRight W (Nat.mul 8 i)) 255) c) n h i hi)
  rw [LCE.bval, List.map_congr_left (g := fun _ => LCE.letV gen c)
    (fun i hi => by rw [hall i (List.mem_range.mp hi)]), List.map_const', List.prod_replicate,
    List.length_range]

@[expose] noncomputable def sigSmall (L : List (List (ℕ × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => mAnd
    (mAnd (Nat.blt (List.rec (motive := fun _ => Nat) 0 (fun _ _ n => Nat.succ n) w) 65536)
      (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => mAnd (Nat.blt (Prod.rec (motive := fun _ => Nat) (fun g _ => g) x) 32768) ih2)
        w)) ih) L

theorem letsSmall : ∀ w : List (ℕ × Bool), List.rec (motive := fun _ => Bool) true
    (fun x _ ih2 => mAnd (Nat.blt (Prod.rec (motive := fun _ => Nat) (fun g _ => g) x) 32768) ih2)
    w = true → ∀ x ∈ w, x.1 < 32768
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: w, h, x, hx => by
    obtain ⟨hy, hw⟩ := mAnd_eq_true h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.blt_eq.mp hy
    · exact letsSmall w hw x hx

theorem lenRec : ∀ u : List (ℕ × Bool),
    List.rec (motive := fun _ => Nat) 0 (fun _ _ n => Nat.succ n) u = u.length
  | [] => rfl
  | _ :: u => congrArg Nat.succ (lenRec u)

theorem sigSmall_spec : ∀ L : List (List (ℕ × Bool)), sigSmall L = true →
    ∀ w ∈ L, (∀ x ∈ w, x.1 < 32768) ∧ w.length < 65536
  | [], _, w, hw => absurd hw List.not_mem_nil
  | v :: L, h, w, hw => by
    obtain ⟨hv, hL⟩ := mAnd_eq_true h
    rcases List.mem_cons.mp hw with rfl | hw
    · obtain ⟨hlen, hlet⟩ := mAnd_eq_true hv
      exact ⟨letsSmall w hlet, by rw [← lenRec]; exact Nat.blt_eq.mp hlen⟩
    · exact sigSmall_spec L hL w hw

theorem card_le_relIndex_mul {G : Type*} [Group G] {K A : Subgroup G} [Finite K]
    (h0 : K.relIndex A ≠ 0) : Finite A ∧ Nat.card A ≤ K.relIndex A * Nat.card K := by
  have e := (K.subgroupOf A).card_mul_index
  have inj : Function.Injective (fun x : K.subgroupOf A =>
      (⟨((x : A) : G), Subgroup.mem_subgroupOf.mp x.2⟩ : K)) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => (z : G)) hxy
  have hfin : Finite (K.subgroupOf A) := Finite.of_injective _ inj
  have hc : Nat.card (K.subgroupOf A) ≤ Nat.card K := Nat.card_le_card_of_injective _ inj
  have hpos : 0 < Nat.card (K.subgroupOf A) := Nat.card_pos
  rw [Subgroup.relIndex] at h0 ⊢
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← e]; exact Nat.mul_ne_zero hpos.ne' h0), ?_⟩
  rw [← e, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ hc

end CFSG.KM24.Words

end
