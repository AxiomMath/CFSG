module

public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.McL.Perm
public import CFSG.Certificates.Kernel.Schur.Pack

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB CFSG.KC

variable {G : Type*} [Group G]

theorem sword_nil (gen : ℕ → G) : sword gen [] = 1 := rfl

theorem sword_cons (gen : ℕ → G) (x : ℕ × Bool) (w : List (ℕ × Bool)) :
    sword gen (x :: w) = (if x.2 then gen x.1 else (gen x.1)⁻¹) * sword gen w := by
  simp [sword]

theorem sword_append (gen : ℕ → G) (u v : List (ℕ × Bool)) :
    sword gen (u ++ v) = sword gen u * sword gen v := by
  simp [sword, List.map_append, List.prod_append]

theorem sword_replicate (gen : ℕ → G) (w : List (ℕ × Bool)) (k : ℕ) :
    sword gen (List.replicate k w).flatten = sword gen w ^ k := by
  induction k with
  | zero => simp [sword]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, sword_append, ih, pow_succ']

@[expose] def winv (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (w.map fun x => (x.1, !x.2)).reverse

theorem sword_winv (gen : ℕ → G) (w : List (ℕ × Bool)) :
    sword gen (winv w) = (sword gen w)⁻¹ := by
  induction w with
  | nil => simp [winv, sword]
  | cons x w ih =>
    have e : winv (x :: w) = winv w ++ [(x.1, !x.2)] := by simp [winv]
    rw [e, sword_append, ih, sword_cons, sword_cons, sword_nil, mul_one, mul_inv_rev]
    congr 1
    cases x.2 <;> simp

@[expose] def subst (ims : ℕ → List (ℕ × Bool)) (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.flatMap fun x => if x.2 then ims x.1 else winv (ims x.1)

theorem sword_subst (gen : ℕ → G) (ims : ℕ → List (ℕ × Bool)) (w : List (ℕ × Bool)) :
    sword gen (subst ims w) = sword (fun i => sword gen (ims i)) w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have e : subst ims (x :: w) =
        (if x.2 then ims x.1 else winv (ims x.1)) ++ subst ims w := by
      simp [subst]
    rw [e, sword_append, ih, sword_cons]
    congr 1
    cases x.2 <;> simp [sword_winv]

@[expose] def tw (gen : ℕ → G) (z : G) (s : ℕ → Bool) : ℕ → G :=
  fun i => if s i then gen i * z else gen i

@[expose] def cnt (s : ℕ → Bool) (w : List (ℕ × Bool)) : ℕ := (w.filter fun x => s x.1).length

theorem sword_tw (gen : ℕ → G) {z : G} (hz : ∀ g, z * g = g * z) (hz2 : z * z = 1)
    (s : ℕ → Bool) (w : List (ℕ × Bool)) :
    sword (tw gen z s) w = sword gen w * z ^ cnt s w := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hcomm : ∀ (g : G) (k : ℕ), z ^ k * g = g * z ^ k := fun g k =>
    (Commute.pow_left (hz g) k)
  have hmove : ∀ (a S : G) (e c : ℕ), a * z ^ e * (S * z ^ c) = a * S * z ^ (c + e) := by
    intro a S e c
    rw [mul_assoc a (z ^ e), ← mul_assoc (z ^ e) S, hcomm S e, mul_assoc S, ← pow_add,
      ← mul_assoc, Nat.add_comm]
  have hlet : ∀ (g : ℕ) (b : Bool), (if b then tw gen z s g else (tw gen z s g)⁻¹) =
      (if b then gen g else (gen g)⁻¹) * z ^ (if s g then 1 else 0) := by
    intro g b
    by_cases hs : s g
    · cases b
      · simp only [tw, hs, ↓reduceIte, Bool.false_eq_true, pow_one, mul_inv_rev, hzi]
        exact (hz _)
      · simp [tw, hs]
    · cases b <;> simp [tw, hs]
  induction w with
  | nil => simp [sword_nil, cnt]
  | cons x w ih =>
    rw [sword_cons, sword_cons, ih]
    obtain ⟨g, b⟩ := x
    have hc : cnt s ((g, b) :: w) = cnt s w + (if s g then 1 else 0) := by
      by_cases hs : s g <;> simp [cnt, hs]
    rw [hlet g b, hc, hmove]

theorem pow_eq_of_sq {z : G} (hz2 : z * z = 1) (k : ℕ) : z ^ k = if k % 2 = 0 then 1 else z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h', hz2]

theorem code_true (g : ℕ) : Schur.Pack.code (g, true) = 2 * g := rfl

theorem code_false (g : ℕ) : Schur.Pack.code (g, false) = 2 * g + 1 := rfl

theorem pk_cons (x : ℕ × Bool) (w : List (ℕ × Bool)) :
    Schur.Pack.pk (x :: w) = Schur.Pack.code x ||| (Schur.Pack.pk w <<< 8) := rfl

theorem code_lt {x : ℕ × Bool} (hx : x.1 < 128) : Schur.Pack.code x < 256 := by
  obtain ⟨g, b⟩ := x
  cases b
  · rw [code_false]
    simp only at hx
    omega
  · rw [code_true]
    simp only at hx
    omega

theorem or_shiftLeft_land {a b : ℕ} (ha : a < 256) : (a ||| (b <<< 8)) &&& 255 = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 8
  · have h255 : (255 : ℕ).testBit i = true := by
      have : (255 : ℕ) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]
      simpa using hi
    simp [h255, show ¬ (8 ≤ i) by omega]
  · have h255 : (255 : ℕ).testBit i = false := by
      have : (255 : ℕ) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]
      simpa using hi
    have ha' : a.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (by
        calc (256 : ℕ) = 2 ^ 8 := rfl
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h255, ha']

theorem or_shiftLeft_shiftRight {a b : ℕ} (ha : a < 256) (k : ℕ) :
    (a ||| (b <<< 8)) >>> (8 * (k + 1)) = b >>> (8 * k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have ha' : a.testBit (8 * (k + 1) + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (by
      calc (256 : ℕ) = 2 ^ 8 := rfl
        _ ≤ 2 ^ (8 * (k + 1) + i) := Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [ha', Bool.false_or]
  have h1 : 8 ≤ 8 * (k + 1) + i := by omega
  simp only [h1, decide_true, Bool.true_and]
  congr 1
  omega

theorem wLet_pk_zero (x : ℕ × Bool) (w : List (ℕ × Bool)) (hx : x.1 < 128) :
    wLet (Schur.Pack.pk (x :: w)) 0 = Schur.Pack.code x := by
  rw [wLet, pk_cons]
  change (Schur.Pack.code x ||| (Schur.Pack.pk w <<< 8)) &&& 255 = Schur.Pack.code x
  exact or_shiftLeft_land (code_lt hx)

theorem wLet_pk_succ (x : ℕ × Bool) (w : List (ℕ × Bool)) (hx : x.1 < 128) (i : ℕ) :
    wLet (Schur.Pack.pk (x :: w)) (i + 1) = wLet (Schur.Pack.pk w) i := by
  rw [wLet, wLet, pk_cons]
  change ((Schur.Pack.code x ||| (Schur.Pack.pk w <<< 8)) >>> (8 * (i + 1))) &&& 255 =
    (Schur.Pack.pk w >>> (8 * i)) &&& 255
  rw [or_shiftLeft_shiftRight (code_lt hx)]

theorem wLet_pk (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < 128) :
    ∀ i (h : i < w.length), wLet (Schur.Pack.pk w) i = Schur.Pack.code w[i] := by
  induction w with
  | nil => intro i h; simp at h
  | cons x w ih =>
    intro i h
    have hx := hw x List.mem_cons_self
    cases i with
    | zero => rw [wLet_pk_zero x w hx]; rfl
    | succ i =>
      rw [wLet_pk_succ x w hx]
      exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) i (by simpa using h)

theorem letV_code (y : ℕ → G) {x : ℕ × Bool} (hx : x.1 < 127) :
    LCE.letV y (Schur.Pack.code x) = if x.2 then y x.1 else (y x.1)⁻¹ := by
  obtain ⟨g, b⟩ := x
  simp only at hx
  cases b
  · rw [code_false]
    have h1 : 2 * g + 1 ≠ 255 := by omega
    have h3 : (2 * g + 1) / 2 = g := by omega
    simp [LCE.letV, h1, h3]
  · rw [code_true]
    have h1 : 2 * g ≠ 255 := by omega
    have h3 : 2 * g / 2 = g := by omega
    simp [LCE.letV, h1, h3]

theorem bval_pk (y : ℕ → G) (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < 127) :
    LCE.bval y (Schur.Pack.pk w) w.length = sword y w := by
  have key : ∀ (v : List (ℕ × Bool)), (∀ x ∈ v, x.1 < 127) →
      ((List.range v.length).map fun i => LCE.letV y (wLet (Schur.Pack.pk v) i)).prod =
        sword y v := by
    intro v
    induction v with
    | nil => intro _; rfl
    | cons x v ih =>
      intro hv
      have hx : x.1 < 127 := hv x List.mem_cons_self
      have hv' : ∀ y ∈ v, y.1 < 127 := fun y hy => hv y (List.mem_cons_of_mem _ hy)
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
        sword_cons, wLet_pk_zero x v (by omega), letV_code y hx]
      congr 1
      rw [← ih hv']
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [wLet_pk_succ x v (by omega)]
  exact key w hw

theorem sword_eq_one_of_evalW {y ψ : ℕ → G} {I : Set ℕ} {MG : ℕ → ℕ} {d g : ℕ}
    (hid : ψ (McL.pid d) = 1)
    (hW : ∀ W n, (∀ i < n, wLet W i < 2 * g) →
      McL.evalW MG d W n ∈ I ∧ ψ (McL.evalW MG d W n) = LCE.bval y W n)
    (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < g) (hg : g < 127) {n : ℕ} (hn : w.length = n)
    (h : Nat.beq (McL.evalW MG d (Schur.Pack.pk w) n) (McL.pid d) = true) :
    sword y w = 1 := by
  subst hn
  have hc : ∀ x : ℕ × Bool, x.1 < g → Schur.Pack.code x < 2 * g := by
    rintro ⟨a, b⟩ hx
    simp only at hx
    cases b
    · rw [code_false]
      omega
    · rw [code_true]
      omega
  have hlet : ∀ i < w.length, wLet (Schur.Pack.pk w) i < 2 * g := by
    intro i hi
    rw [wLet_pk w (fun x hx => by have := hw x hx; omega) i hi]
    exact hc _ (hw _ (List.getElem_mem hi))
  have h2 := (hW _ _ hlet).2
  rw [Nat.eq_of_beq_eq_true h, hid, bval_pk y w (fun x hx => by have := hw x hx; omega)] at h2
  exact h2.symm

end CertificateChecks.KernelSchur

end
