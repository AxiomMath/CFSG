module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.FiveKVals

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22FiveK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W

@[expose] noncomputable def pwK (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 3510 12) (fun _ acc => Fi22X.c p acc) k

@[expose] noncomputable def planeK (X Y i j : Nat) : Nat := Fi22X.c (pwK X i) (pwK Y j)

@[expose] noncomputable def nProdK (N1 N2 : Nat) (w : List Nat) : Nat :=
  w.foldr (fun k A => Fi22X.c (if k = 1 then N1 else N2) A) (pidn 3510 12)

@[expose] noncomputable def conjK (X Y N1 N2 : Nat) (t : Nat × Nat × List Nat) : Bool :=
  strictB (nProdK N1 N2 t.2.2) fun P =>
    Nat.beq (Fi22X.c P X) (Fi22X.c (planeK X Y t.1 t.2.1) P)

@[expose] noncomputable def orbK (X Y N1 N2 : Nat) : Bool :=
  Fi22X.cn X && Fi22X.cn Y && Fi22X.cn N1 && Fi22X.cn N2 &&
  Nat.beq (pwK X 5) (pidn 3510 12) && Nat.beq (pwK Y 5) (pidn 3510 12) &&
  Nat.beq (Fi22X.c X Y) (Fi22X.c Y X) &&
  allN 5 (fun i => allN 5 fun j => (i == 0 && j == 0) || !(Nat.beq (planeK X Y i j) (pidn 3510 12))) &&
  Nat.beq (Fi22X.c N1 X) (Fi22X.c (planeK X Y 2 3) N1) &&
  Nat.beq (Fi22X.c N1 Y) (Fi22X.c (planeK X Y 1 2) N1) &&
  Nat.beq (Fi22X.c N2 X) (Fi22X.c (planeK X Y 4 1) N2) &&
  Nat.beq (Fi22X.c N2 Y) (Fi22X.c (planeK X Y 1 1) N2)

@[expose] noncomputable def genK (X Y H N1 N2 Z : Nat) : Bool :=
  Fi22X.cn X && Fi22X.cn Y && Fi22X.cn H && Fi22X.cn N1 && Fi22X.cn N2 && Fi22X.cn Z &&
  permOK 3510 12 (mask 12) (3510 * 12) X (Fi22X.inv X) &&
  permOK 3510 12 (mask 12) (3510 * 12) Y (Fi22X.inv Y) &&
  permOK 3510 12 (mask 12) (3510 * 12) H (Fi22X.inv H) &&
  permOK 3510 12 (mask 12) (3510 * 12) N1 (Fi22X.inv N1) &&
  permOK 3510 12 (mask 12) (3510 * 12) N2 (Fi22X.inv N2) &&
  permOK 3510 12 (mask 12) (3510 * 12) Z (Fi22X.inv Z) &&
  Nat.beq (Fi22X.c Z X) (Fi22X.c (pwK X 2) Z)

namespace Slp

@[expose] noncomputable def slpL (z : Int) : Nat :=
  Bool.rec (GI ((Nat.shiftRight (Mathieu.icode z) 1).sub 1))
    (G ((Nat.shiftRight (Mathieu.icode z) 1).sub 1)) ((Nat.land (Mathieu.icode z) 1).beq 0)

@[expose] def slpOk (u : List Int) : Bool := u.all fun z => z == 1 || z == -1 || z == 2 || z == -2

theorem c_assoc {p q r : Nat} (hp : Fi22X.cn p = true) (hr : Fi22X.cn r = true) :
    Fi22X.c (Fi22X.c p q) r = Fi22X.c p (Fi22X.c q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : 3510 < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  unfold Fi22X.c
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem c_idL {p : Nat} (hp : Fi22X.cn p = true) : Fi22X.c (pidn 3510 12) p = p := by
  obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hp
  have hn32 : 3510 < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  unfold Fi22X.c
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]

theorem c_idR {p : Nat} (hp : Fi22X.cn p = true) : Fi22X.c p (pidn 3510 12) = p := by
  obtain ⟨hn, hw, hp0, -⟩ := PF.canon_facts hp
  have hn32 : 3510 < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  unfold Fi22X.c
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]

theorem W_cons (z : Int) (u : List Int) : W (z :: u) = Fi22X.c (slpL z) (W u) := by
  change strictN (W u) (fun T => strictN (Mathieu.icode z) fun c => pcomp 3510 12 (mask 12)
    (Bool.rec (GI ((Nat.shiftRight c 1).sub 1)) (G ((Nat.shiftRight c 1).sub 1))
      ((Nat.land c 1).beq 0)) T) = _
  simp only [PF.strictN_eqP]
  rfl

theorem slpL_cn {z : Int} (h : (z == 1 || z == -1 || z == 2 || z == -2) = true) :
    Fi22X.cn (slpL z) = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h
  · exact (gen_cn (k := 0) (by omega)).1
  · exact (gen_cn (k := 0) (by omega)).2
  · exact (gen_cn (k := 1) (by omega)).1
  · exact (gen_cn (k := 1) (by omega)).2

theorem W_cn : ∀ u : List Int, slpOk u = true → Fi22X.cn (W u) = true
  | [] => fun _ => cnId
  | z :: u => fun h => by
    simp only [slpOk, List.all_cons, Bool.and_eq_true] at h
    rw [W_cons]
    exact Fi22X.cn_c (slpL_cn h.1) (W_cn u h.2)

theorem W_app : ∀ u v : List Int, slpOk u = true → Fi22X.cn (W v) = true →
    W (u ++ v) = Fi22X.c (W u) (W v)
  | [], v => fun _ hv => (c_idL hv).symm
  | z :: u, v => fun h hv => by
    have h' := h
    simp only [slpOk, List.all_cons, Bool.and_eq_true] at h'
    rw [List.cons_append, W_cons, W_cons, W_app u v h'.2 hv]
    exact (c_assoc (slpL_cn h'.1) hv).symm

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

@[expose] def slpEStep (E : List (List Int)) (p : Nat × Nat) : List (List Int) :=
  E ++ [E.getD p.1 [] ++ E.getD p.2 []]

@[expose] noncomputable def slpVStep (V : List Nat) (p : Nat × Nat) : List Nat :=
  strictL (Fi22X.c (V.getD p.1 (pidn 3510 12)) (V.getD p.2 (pidn 3510 12))) fun v => V ++ [v]

@[expose] def slpE (R : List (Nat × Nat)) : List (List Int) :=
  R.foldl slpEStep [[1], [-1], [2], [-2]]

@[expose] noncomputable def slpV (R : List (Nat × Nat)) : List Nat :=
  R.foldl slpVStep [slpL 1, slpL (-1), slpL 2, slpL (-2)]

def SlpInv (E : List (List Int)) (V : List Nat) : Prop :=
  E.length = V.length ∧ ∀ i, slpOk (E.getD i []) = true ∧
    V.getD i (pidn 3510 12) = W (E.getD i []) ∧ Fi22X.cn (V.getD i (pidn 3510 12)) = true

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : Nat) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp

theorem slpInv_step {E : List (List Int)} {V : List Nat} (h : SlpInv E V) (a b : Nat) :
    SlpInv (E ++ [E.getD a [] ++ E.getD b []])
      (V ++ [Fi22X.c (V.getD a (pidn 3510 12)) (V.getD b (pidn 3510 12))]) := by
  obtain ⟨hl, hi⟩ := h
  refine ⟨by simp [hl], fun i => ?_⟩
  rw [getD_snoc, getD_snoc, ← hl]
  split_ifs
  · exact hi i
  · obtain ⟨oa, va, ca⟩ := hi a
    obtain ⟨ob, vb, cb⟩ := hi b
    refine ⟨?_, ?_, Fi22X.cn_c ca cb⟩
    · simp only [slpOk, List.all_append, Bool.and_eq_true]
      exact ⟨oa, ob⟩
    · rw [W_app _ _ oa (vb ▸ cb), ← va, ← vb]
  · exact ⟨rfl, rfl, cnId⟩

theorem slpInv_fold : ∀ (R : List (Nat × Nat)) (E : List (List Int)) (V : List Nat), SlpInv E V →
    SlpInv (R.foldl slpEStep E) (R.foldl slpVStep V)
  | [], _, _, h => h
  | p :: R, E, V, h => by
    rw [List.foldl_cons, List.foldl_cons, slpVStep, strictL_eq]
    exact slpInv_fold R _ _ (slpInv_step h p.1 p.2)

theorem W_one {z : Int} (h : (z == 1 || z == -1 || z == 2 || z == -2) = true) :
    W [z] = slpL z := by
  rw [W_cons]
  exact c_idR (slpL_cn h)

theorem slp_sound (R : List (Nat × Nat)) : SlpInv (slpE R) (slpV R) := by
  refine slpInv_fold R _ _ ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact ⟨rfl, (W_one (z := 1) rfl).symm, slpL_cn (z := 1) rfl⟩
  | 1 =>
    refine ⟨rfl, ?_, ?_⟩ <;> simp only [List.getD_cons_succ, List.getD_cons_zero]
    · exact (W_one (z := -1) rfl).symm
    · exact slpL_cn (z := -1) rfl
  | 2 => exact ⟨rfl, (W_one (z := 2) rfl).symm, slpL_cn (z := 2) rfl⟩
  | 3 =>
    refine ⟨rfl, ?_, ?_⟩ <;> simp only [List.getD_cons_succ, List.getD_cons_zero]
    · exact (W_one (z := -2) rfl).symm
    · exact slpL_cn (z := -2) rfl
  | _ + 4 => exact ⟨rfl, rfl, cnId⟩

@[expose] def beqNL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a b && beqNL l m
  | _, _ => false

theorem beqNL_eq : ∀ {l m : List Nat}, beqNL l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [beqNL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, beqNL_eq h.2]
  | [], _ :: _, h => by simp [beqNL] at h
  | _ :: _, [], h => by simp [beqNL] at h

@[expose] noncomputable def slpSelV (V : List Nat) (I : List Nat) : List Nat :=
  I.map fun i => V.getD i (pidn 3510 12)

@[expose] def slpSelE (E : List (List Int)) (I : List Nat) : List (List Int) :=
  I.map fun i => E.getD i []

theorem sel_get {E : List (List Int)} {V : List Nat} (h : SlpInv E V) : ∀ (I : List Nat) (j : Nat),
    slpOk ((slpSelE E I).getD j []) = true ∧
      (slpSelV V I).getD j (pidn 3510 12) = W ((slpSelE E I).getD j []) ∧
      Fi22X.cn ((slpSelV V I).getD j (pidn 3510 12)) = true
  | [], _ => ⟨rfl, rfl, cnId⟩
  | i :: _, 0 => h.2 i
  | _ :: I, j + 1 => sel_get h I j

theorem seg_step {E : List (List Int)} {V : List Nat} (h : SlpInv E V) (R : List (Nat × Nat))
    (I L : List Nat) (hc : beqNL (slpSelV (R.foldl slpVStep V) I) L = true) :
    SlpInv (slpSelE (R.foldl slpEStep E) I) L := by
  rw [← beqNL_eq hc]
  exact ⟨by simp [slpSelE, slpSelV], sel_get (slpInv_fold R E V h) I⟩

end Slp

theorem seg0OK : Slp.beqNL (Slp.slpSelV (segR0.foldl Slp.slpVStep (Slp.slpV [])) segI0) segL0 =
    true := by quickRfl

theorem seg1OK : Slp.beqNL (Slp.slpSelV (segR1.foldl Slp.slpVStep segL0) segI1) segL1 = true := by
  quickRfl

theorem seg2OK : Slp.beqNL (Slp.slpSelV (segR2.foldl Slp.slpVStep segL1) segI2) segL2 = true := by
  quickRfl

@[expose] def fiveE : List (List Int) :=
  Slp.slpSelE (segR2.foldl Slp.slpEStep (Slp.slpSelE (segR1.foldl Slp.slpEStep
    (Slp.slpSelE (segR0.foldl Slp.slpEStep (Slp.slpE [])) segI0)) segI1)) segI2

theorem fiveInv : Slp.SlpInv fiveE segL2 :=
  Slp.seg_step (Slp.seg_step (Slp.seg_step (Slp.slp_sound []) segR0 segI0 segL0 seg0OK) segR1 segI1
    segL1 seg1OK) segR2 segI2 segL2 seg2OK

theorem five_W (j : Nat) {w : List Int} (h : fiveE.getD j [] = w) :
    W w = segL2.getD j (pidn 3510 12) := by
  obtain ⟨-, e, -⟩ := fiveInv.2 j
  rw [← h, e]

@[expose] noncomputable def bothK (l : List Nat) : Bool :=
  strictB (l.getD 0 (pidn 3510 12)) fun X => strictB (l.getD 1 (pidn 3510 12)) fun Y =>
    strictB (l.getD 2 (pidn 3510 12)) fun H => strictB (l.getD 3 (pidn 3510 12)) fun N1 =>
      strictB (l.getD 4 (pidn 3510 12)) fun N2 => strictB (l.getD 5 (pidn 3510 12)) fun Z =>
        orbK X Y N1 N2 && genK X Y H N1 N2 Z

theorem bothOK : bothK segL2 = true := by quickRfl

theorem fiveWordsOK : (fiveE.getD 0 [] == signedWord wx && fiveE.getD 1 [] == signedWord wy &&
    fiveE.getD 3 [] == nw1 && fiveE.getD 4 [] == nw2 && fiveE.getD 2 [] == hw &&
    fiveE.getD 5 [] == zw) = true := by decide +kernel

theorem lettersOK' : (signedWord wx :: signedWord wy :: nw1 :: nw2 :: hw :: [zw]).all
    (lettersK 2) = true := by quickRfl

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pw_eq {p : Nat} (hp : Fi22X.cn p = true) :
    ∀ k, pw (unpack 3510 12 p) k = unpack 3510 12 (pwK p k) ∧ Fi22X.cn (pwK p k) = true
  | 0 => ⟨(idK_sound idOK).symm, cnId⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := pw_eq hp k
    have e : pw (unpack 3510 12 p) (k + 1) = compA 3510 (unpack 3510 12 p) (pw (unpack 3510 12 p) k) :=
      rfl
    have e2 : pwK p (k + 1) = Fi22X.c p (pwK p k) := rfl
    rw [e, e2, ih1, Fi22X.comp_eq hp ih2]
    exact ⟨rfl, Fi22X.cn_c hp ih2⟩

theorem hI : idA 3510 = unpack 3510 12 (pidn 3510 12) := (idK_sound idOK).symm

theorem comp_beq {p q r s : Nat} (hp : Fi22X.cn p = true) (hq : Fi22X.cn q = true)
    (hr : Fi22X.cn r = true) (hs : Fi22X.cn s = true) :
    eqA 3510 (compA 3510 (unpack 3510 12 p) (unpack 3510 12 q))
      (compA 3510 (unpack 3510 12 r) (unpack 3510 12 s)) =
      Nat.beq (Fi22X.c p q) (Fi22X.c r s) := by
  rw [Fi22X.comp_eq hp hq, Fi22X.comp_eq hr hs]
  exact eqA_unpack (Fi22X.cn_c hp hq) (Fi22X.cn_c hr hs)

namespace Pl

section Plane

variable {M : Type} [Monoid M]

@[expose] def pl (x y : M) (a b : Nat) : M := x ^ a * y ^ b

theorem pow_mod5 {z : M} (h : z ^ 5 = 1) (n : Nat) : z ^ n = z ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h, one_pow, one_mul]

variable {x y : M} (hc : Commute x y) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
include hc hx hy

theorem pl_mul (a b c d : Nat) : pl x y a b * pl x y c d = pl x y ((a + c) % 5) ((b + d) % 5) := by
  unfold pl
  rw [← pow_mod5 hx, ← pow_mod5 hy, pow_add, pow_add]
  calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * ((y ^ b * x ^ c) * y ^ d) := by
        simp only [mul_assoc]
    _ = x ^ a * ((x ^ c * y ^ b) * y ^ d) := by rw [← (hc.pow_pow c b).eq]
    _ = x ^ a * x ^ c * (y ^ b * y ^ d) := by simp only [mul_assoc]

theorem pl_pow (p q : Nat) : ∀ n, pl x y p q ^ n = pl x y (p * n % 5) (q * n % 5)
  | 0 => by simp [pl]
  | n + 1 => by
    rw [pow_succ, pl_pow p q n, pl_mul hc hx hy, Nat.mul_succ, Nat.mul_succ]
    congr 1 <;> omega

theorem semi_pl {N : M} {p q r s : Nat} (h1 : SemiconjBy N x (pl x y p q))
    (h2 : SemiconjBy N y (pl x y r s)) (a b : Nat) :
    SemiconjBy N (pl x y a b) (pl x y ((p * a + r * b) % 5) ((q * a + s * b) % 5)) := by
  have h := (h1.pow_right a).mul_right (h2.pow_right b)
  rw [pl_pow hc hx hy, pl_pow hc hx hy, pl_mul hc hx hy] at h
  have e1 : (p * a + r * b) % 5 = (p * a % 5 + r * b % 5) % 5 := by omega
  have e2 : (q * a + s * b) % 5 = (q * a % 5 + s * b % 5) % 5 := by omega
  rw [e1, e2]
  exact h

end Plane

@[expose] def actS (k : Nat) (v : Nat × Nat) : Nat × Nat :=
  if k = 1 then ((2 * v.1 + 1 * v.2) % 5, (3 * v.1 + 2 * v.2) % 5)
  else ((4 * v.1 + 1 * v.2) % 5, (1 * v.1 + 1 * v.2) % 5)

@[expose] def act (w : List Nat) : Nat × Nat := w.foldr actS (1, 0)

section Word

variable {M : Type} [Monoid M]

@[expose] def nS (N1 N2 : M) (w : List Nat) : M := w.foldr (fun k A => (if k = 1 then N1 else N2) * A) 1

variable {x y N1 N2 : M} (hc : Commute x y) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
  (a1 : SemiconjBy N1 x (pl x y 2 3)) (a2 : SemiconjBy N1 y (pl x y 1 2))
  (b1 : SemiconjBy N2 x (pl x y 4 1)) (b2 : SemiconjBy N2 y (pl x y 1 1))
include hc hx hy a1 a2 b1 b2

theorem semi_word : ∀ w, SemiconjBy (nS N1 N2 w) x (pl x y (act w).1 (act w).2)
  | [] => by
    have e : pl x y 1 0 = x := by simp [pl]
    change SemiconjBy 1 x (pl x y 1 0)
    rw [e]
    exact SemiconjBy.one_left x
  | k :: w => by
    have ih := semi_word w
    change SemiconjBy ((if k = 1 then N1 else N2) * nS N1 N2 w) x (pl x y (actS k (act w)).1
      (actS k (act w)).2)
    by_cases hk : k = 1
    · simp only [actS, hk, ↓reduceIte]
      exact (semi_pl hc hx hy a1 a2 _ _).mul_left ih
    · simp only [actS, hk, ↓reduceIte]
      exact (semi_pl hc hx hy b1 b2 _ _).mul_left ih

end Word

abbrev S : Type := {p : Nat // Fi22X.cn p = true}

noncomputable instance : Monoid S where
  mul a b := ⟨Fi22X.c a.1 b.1, Fi22X.cn_c a.2 b.2⟩
  one := ⟨pidn 3510 12, cnId⟩
  mul_assoc a b c := Subtype.ext (Slp.c_assoc a.2 c.2)
  one_mul a := Subtype.ext (Slp.c_idL a.2)
  mul_one a := Subtype.ext (Slp.c_idR a.2)

theorem pwK_val {X : Nat} (cX : Fi22X.cn X = true) : ∀ i, ((⟨X, cX⟩ : S) ^ i).1 = pwK X i
  | 0 => rfl
  | i + 1 => by
    rw [pow_succ']
    change Fi22X.c X ((⟨X, cX⟩ : S) ^ i).1 = Fi22X.c X (pwK X i)
    rw [pwK_val cX i]

theorem pl_val {X Y : Nat} (cX : Fi22X.cn X = true) (cY : Fi22X.cn Y = true) (i j : Nat) :
    (pl (⟨X, cX⟩ : S) ⟨Y, cY⟩ i j).1 = planeK X Y i j := by
  change Fi22X.c ((⟨X, cX⟩ : S) ^ i).1 ((⟨Y, cY⟩ : S) ^ j).1 = _
  rw [pwK_val, pwK_val]
  rfl

theorem nS_val {N1 N2 : Nat} (c1 : Fi22X.cn N1 = true) (c2 : Fi22X.cn N2 = true) :
    ∀ w, (nS (⟨N1, c1⟩ : S) ⟨N2, c2⟩ w).1 = nProdK N1 N2 w
  | [] => rfl
  | k :: w => by
    change Fi22X.c (if k = 1 then (⟨N1, c1⟩ : S) else ⟨N2, c2⟩).1 (nS (⟨N1, c1⟩ : S) ⟨N2, c2⟩ w).1 =
      Fi22X.c (if k = 1 then N1 else N2) (nProdK N1 N2 w)
    rw [nS_val c1 c2 w]
    split_ifs <;> rfl

theorem semi_of {N Q P : S} {Pv : Nat} (hP : P.1 = Pv)
    (h : Nat.beq (Fi22X.c N.1 Q.1) (Fi22X.c Pv N.1) = true) : SemiconjBy N Q P :=
  Subtype.ext (by
    change Fi22X.c N.1 Q.1 = Fi22X.c P.1 N.1
    rw [hP]
    exact Nat.eq_of_beq_eq_true h)

end Pl

theorem planeCoverOK : allN 5 (fun i => allN 5 fun j => (i == 0 && j == 0) ||
    conjWords.any fun t => t.1 == i && t.2.1 == j && Pl.act t.2.2 == (t.1, t.2.1)) = true := by
  decide +kernel

section Sound

variable {X Y N1 N2 : Nat} (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y)
  (h1 : n1A = unpack 3510 12 N1) (h2 : n2A = unpack 3510 12 N2)
  (cX : Fi22X.cn X = true) (cY : Fi22X.cn Y = true) (c1 : Fi22X.cn N1 = true)
  (c2 : Fi22X.cn N2 = true)
include hX hY cX cY

theorem plane_eq (i j : Nat) :
    planeA i j = unpack 3510 12 (planeK X Y i j) ∧ Fi22X.cn (planeK X Y i j) = true := by
  obtain ⟨a1, a2⟩ := pw_eq cX i
  obtain ⟨b1, b2⟩ := pw_eq cY j
  unfold planeA planeK
  rw [hX, hY, a1, b1, Fi22X.comp_eq a2 b2]
  exact ⟨rfl, Fi22X.cn_c a2 b2⟩

omit hX hY cX cY in
include h1 h2 c1 c2 in
theorem nProd_eq : ∀ w : List Nat,
    nProd w = unpack 3510 12 (nProdK N1 N2 w) ∧ Fi22X.cn (nProdK N1 N2 w) = true
  | [] => ⟨hI, cnId⟩
  | k :: w => by
    obtain ⟨ih1, ih2⟩ := nProd_eq w
    have e : nProd (k :: w) = compA 3510 (if k = 1 then n1A else n2A) (nProd w) := rfl
    have e2 : nProdK N1 N2 (k :: w) = Fi22X.c (if k = 1 then N1 else N2) (nProdK N1 N2 w) := rfl
    rw [e, e2, ih1]
    by_cases hk : k = 1
    · rw [if_pos hk, if_pos hk, h1, Fi22X.comp_eq c1 ih2]
      exact ⟨rfl, Fi22X.cn_c c1 ih2⟩
    · rw [if_neg hk, if_neg hk, h2, Fi22X.comp_eq c2 ih2]
      exact ⟨rfl, Fi22X.cn_c c2 ih2⟩

include h1 h2 c1 c2 in
theorem conj_eq (t : Nat × Nat × List Nat) : conjOK t = conjK X Y N1 N2 t := by
  obtain ⟨p1, p2⟩ := nProd_eq h1 h2 c1 c2 t.2.2
  obtain ⟨q1, q2⟩ := plane_eq hX hY cX cY t.1 t.2.1
  unfold conjOK conjK
  rw [strictB_eq', p1, q1, hX, Fi22X.comp_eq p2 cX, Fi22X.comp_eq q2 p2]
  exact eqA_unpack (Fi22X.cn_c p2 cX) (Fi22X.cn_c q2 p2)

include h1 h2 c1 c2 in
theorem conj_true (k5 : Nat.beq (pwK X 5) (pidn 3510 12) = true)
    (k6 : Nat.beq (pwK Y 5) (pidn 3510 12) = true) (k7 : Nat.beq (Fi22X.c X Y) (Fi22X.c Y X) = true)
    (k9 : Nat.beq (Fi22X.c N1 X) (Fi22X.c (planeK X Y 2 3) N1) = true)
    (k10 : Nat.beq (Fi22X.c N1 Y) (Fi22X.c (planeK X Y 1 2) N1) = true)
    (k11 : Nat.beq (Fi22X.c N2 X) (Fi22X.c (planeK X Y 4 1) N2) = true)
    (k12 : Nat.beq (Fi22X.c N2 Y) (Fi22X.c (planeK X Y 1 1) N2) = true)
    {t : Nat × Nat × List Nat} (ht : Pl.act t.2.2 = (t.1, t.2.1)) : conjOK t = true := by
  rw [conj_eq hX hY h1 h2 cX cY c1 c2]
  have hx : (⟨X, cX⟩ : Pl.S) ^ 5 = 1 := Subtype.ext (by
    rw [Pl.pwK_val]
    exact Nat.eq_of_beq_eq_true k5)
  have hy : (⟨Y, cY⟩ : Pl.S) ^ 5 = 1 := Subtype.ext (by
    rw [Pl.pwK_val]
    exact Nat.eq_of_beq_eq_true k6)
  have hc : Commute (⟨X, cX⟩ : Pl.S) ⟨Y, cY⟩ := Subtype.ext (Nat.eq_of_beq_eq_true k7)
  have h := Pl.semi_word hc hx hy (N1 := ⟨N1, c1⟩) (N2 := ⟨N2, c2⟩)
    (Pl.semi_of (Pv := planeK X Y 2 3) (Pl.pl_val cX cY 2 3) k9)
    (Pl.semi_of (Pv := planeK X Y 1 2) (Pl.pl_val cX cY 1 2) k10)
    (Pl.semi_of (Pv := planeK X Y 4 1) (Pl.pl_val cX cY 4 1) k11)
    (Pl.semi_of (Pv := planeK X Y 1 1) (Pl.pl_val cX cY 1 1) k12) t.2.2
  rw [ht] at h
  have h' : Fi22X.c (Pl.nS (⟨N1, c1⟩ : Pl.S) ⟨N2, c2⟩ t.2.2).1 X =
      Fi22X.c (Pl.pl (⟨X, cX⟩ : Pl.S) ⟨Y, cY⟩ t.1 t.2.1).1
        (Pl.nS (⟨N1, c1⟩ : Pl.S) ⟨N2, c2⟩ t.2.2).1 :=
    congrArg Subtype.val h
  unfold conjK
  rw [strictB_eq', ← Pl.nS_val c1 c2, ← Pl.pl_val cX cY, h']
  exact Nat.beq_refl _

include h1 h2 c1 c2 in
theorem orb_of (hl : (lettersOK 2 (signedWord wx) && lettersOK 2 (signedWord wy) &&
      lettersOK 2 nw1 && lettersOK 2 nw2) = true)
    (h : orbK X Y N1 N2 = true) : orbCheck = true := by
  unfold orbK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, k5, k6, k7, k8, k9, k10, k11, k12⟩ := h
  simp only [Bool.and_eq_true, and_assoc] at hl
  obtain ⟨l1, l2, l3, l4⟩ := hl
  obtain ⟨x5, cx5⟩ := pw_eq cX 5
  obtain ⟨y5, cy5⟩ := pw_eq cY 5
  have pl := plane_eq hX hY cX cY
  unfold orbCheck
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨l1, l2, l3, l4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX, x5, hI, eqA_unpack cx5 cnId]
    exact k5
  · rw [hY, y5, hI, eqA_unpack cy5 cnId]
    exact k6
  · unfold commA
    rw [hX, hY, comp_beq cX cY cY cX]
    exact k7
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have k := allN_spec (allN_spec k8 i hi) j hj
    rw [(pl i j).1, hI, eqA_unpack (pl i j).2 cnId]
    exact k
  · rw [h1, hX, (pl 2 3).1, comp_beq c1 cX (pl 2 3).2 c1]
    exact k9
  · rw [h1, hY, (pl 1 2).1, comp_beq c1 cY (pl 1 2).2 c1]
    exact k10
  · rw [h2, hX, (pl 4 1).1, comp_beq c2 cX (pl 4 1).2 c2]
    exact k11
  · rw [h2, hY, (pl 1 1).1, comp_beq c2 cY (pl 1 1).2 c2]
    exact k12
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have k := allN_spec (allN_spec planeCoverOK i hi) j hj
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at k ⊢
    rcases k with k | ⟨t, ht, ⟨e1, e2⟩, e3⟩
    · exact Or.inl k
    · exact Or.inr ⟨t, ht, ⟨e1, e2⟩, conj_true hX hY h1 h2 cX cY c1 c2 k5 k6 k7 k9 k10 k11 k12 e3⟩

end Sound

theorem both_parts : (orbK (W (signedWord wx)) (W (signedWord wy)) (W nw1) (W nw2) &&
    genK (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw)) = true := by
  have hw' := fiveWordsOK
  simp only [Bool.and_eq_true, beq_iff_eq] at hw'
  obtain ⟨⟨⟨⟨⟨ex, ey⟩, e1⟩, e2⟩, eh⟩, ez⟩ := hw'
  have h := bothOK
  unfold bothK at h
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq'] at h
  rw [five_W 0 ex, five_W 1 ey, five_W 3 e1, five_W 4 e2, five_W 2 eh, five_W 5 ez]
  exact h

theorem orb_parts : orbK (W (signedWord wx)) (W (signedWord wy)) (W nw1) (W nw2) = true := by
  have h := both_parts
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem gen_parts : genK (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw) =
    true := by
  have h := both_parts
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem letters : lettersK 2 (signedWord wx) = true ∧ lettersK 2 (signedWord wy) = true ∧
    lettersK 2 nw1 = true ∧ lettersK 2 nw2 = true ∧ lettersK 2 hw = true ∧
    lettersK 2 zw = true := by
  have h := lettersOK'
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact h

theorem eval_eq {w : List Int} (hl : lettersK 2 w = true) : evalW w = unpack 3510 12 (W w) :=
  word_eq orig_bind hl

theorem x_eq : xA = unpack 3510 12 (W (signedWord wx)) := eval_eq letters.1
theorem y_eq : yA = unpack 3510 12 (W (signedWord wy)) := eval_eq letters.2.1
theorem n1_eq : n1A = unpack 3510 12 (W nw1) := eval_eq letters.2.2.1
theorem n2_eq : n2A = unpack 3510 12 (W nw2) := eval_eq letters.2.2.2.1
theorem h_eq : hA = unpack 3510 12 (W hw) := eval_eq letters.2.2.2.2.1
theorem z_eq : zA = unpack 3510 12 (W zw) := eval_eq letters.2.2.2.2.2

theorem orbK_cn {X Y N1 N2 : Nat} (h : orbK X Y N1 N2 = true) :
    Fi22X.cn X = true ∧ Fi22X.cn Y = true ∧ Fi22X.cn N1 = true ∧ Fi22X.cn N2 = true := by
  unfold orbK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem orb : orbCheck = true := by
  have h := orb_parts
  obtain ⟨cX, cY, c1, c2⟩ := orbK_cn h
  exact orb_of x_eq y_eq n1_eq n2_eq cX cY c1 c2 (by decide +kernel) h

theorem gen_of {X Y H N1 N2 Z : Nat} (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y)
    (hH : hA = unpack 3510 12 H) (h1 : n1A = unpack 3510 12 N1) (h2 : n2A = unpack 3510 12 N2)
    (hZ : zA = unpack 3510 12 Z) (h : genK X Y H N1 N2 Z = true) : genCheck = true := by
  unfold genK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨cX, -, -, -, -, cZ, pX, pY, pH, p1, p2, pZ, kz⟩ := h
  obtain ⟨x2, cx2⟩ := pw_eq cX 2
  have hInv : ∀ k < 6, isInvA 3510 gens6A[k]! gens6Inv[k]! = true := by
    intro k hk
    have e : gens6Inv[k]! = invCand 3510 gens6A[k]! := by
      rw [getElem!_pos _ k (by simp [gens6Inv, gens6A]; omega),
        getElem!_pos gens6A k (by simp [gens6A]; omega)]
      simp [gens6Inv]
    rw [e]
    interval_cases k
    · have e0 : gens6A[0]! = xA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hX pX
    · have e0 : gens6A[1]! = yA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hY pY
    · have e0 : gens6A[2]! = hA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hH pH
    · have e0 : gens6A[3]! = n1A := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of h1 p1
    · have e0 : gens6A[4]! = n2A := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of h2 p2
    · have e0 : gens6A[5]! = zA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hZ pZ
  have hz : eqA 3510 (compA 3510 zA xA) (compA 3510 (pw xA 2) zA) = true := by
    rw [hX, hZ, x2, comp_beq cZ cX cx2 cZ]
    exact kz
  have hl : (lettersOK 2 zw && lettersOK 6 g1w && lettersOK 6 g2w) = true := by decide +kernel
  simp only [Bool.and_eq_true] at hl
  unfold genCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hl.1.1, hz⟩, hl.1.2⟩, hl.2⟩, CFSG.Monster.B.Co2.allLt_iff.2 hInv⟩

theorem gen : genCheck = true := gen_of x_eq y_eq h_eq n1_eq n2_eq z_eq gen_parts

end CertificateChecks.KernelSpor.Fi22FiveK

end
