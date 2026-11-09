module

public meta import Lean
public import Certificates.Data.Kernel.Q7Bits.Defs

public section

namespace CFSG.Certificates.Kernel.Q7Bits.Rec

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

theorem force_eq {β : Sort _} (y : Nat) (k : Nat → β) : forceN y k = k y := by
  unfold forceN
  cases h : Nat.beq y 0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]
    rfl

@[expose] def ladd (x y : P3) : P3 := laddK x y id

theorem laddK_eq {β : Sort _} (x y : P3) (k : P3 → β) : laddK x y k = k (ladd x y) := by
  simp only [ladd, laddK, force_eq, id]

@[expose] def sumA : P3 → List P3 → P3
  | a, [] => a
  | a, x :: l => sumA (ladd a x) l

theorem sumAK_eq {β : Sort _} (a : P3) (l : List P3) (k : P3 → β) :
    sumAK a l k = k (sumA a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [sumAK, laddK_eq, ih, sumA]

@[expose] def sumP : List P3 → P3
  | [] => z3
  | x :: l => sumA x l

theorem sumK_eq {β : Sort _} (l : List P3) (k : P3 → β) : sumK l k = k (sumP l) := by
  cases l <;> simp only [sumK, sumP, sumAK_eq]

@[expose] def orP : Option Nat → Bool → Nat → Option Nat
  | none, b, q => bif b then some q else none
  | some a, b, q => bif b then some (Nat.lor a q) else some a

theorem orO_eq {β : Sort _} (a : Option Nat) (b : Bool) (q : Nat) (k : Option Nat → β) :
    orO a b q k = k (orP a b q) := by
  cases a <;> cases b <;> simp only [orO, orP, Bool.cond_true, Bool.cond_false, force_eq]

@[expose] def selP (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 : Nat) : Nat :=
  (orP (orP (orP (orP (orP (orP (orP (orP none ((t 0).testBit j) q0) ((t 1).testBit j) q1)
    ((t 2).testBit j) q2) ((t 3).testBit j) q3) ((t 4).testBit j) q4) ((t 5).testBit j) q5)
    ((t 6).testBit j) q6) ((t 0).testBit j) q7).getD 0

theorem selK_eq {β : Sort _} (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 : Nat)
    (k : Nat → β) : selK t j q0 q1 q2 q3 q4 q5 q6 q7 k = k (selP t j q0 q1 q2 q3 q4 q5 q6 q7) := by
  simp only [selK, orO_eq, selP]

@[expose] def lmap (m : Nat) (x : P3) (t : Nat → Nat) : P3 := lmapK m x t id

theorem lmapK_eq {β : Sort _} (m : Nat) (x : P3) (t : Nat → Nat) (k : P3 → β) :
    lmapK m x t k = k (lmap m x t) := by
  simp only [lmap, lmapK, force_eq, selK_eq, id]

@[expose] def tblA (m : Nat) (x : P3) : List Nat → List P3
  | [] => []
  | j :: js => lmap m x (fun v => j * v % 7) :: tblA m x js

theorem tblAK_eq {β : Sort _} (m : Nat) (x : P3) (js : List Nat) (k : List P3 → β) :
    tblAK m x js k = k (tblA m x js) := by
  induction js generalizing k with
  | nil => rfl
  | cons j js ih => simp only [tblAK, lmapK_eq, ih, tblA]

@[expose] def tbl (m : Nat) (x : P3) : List P3 := z3 :: x :: tblA m x [2, 3, 4, 5, 6]

theorem tblK_eq {β : Sort _} (m : Nat) (x : P3) (k : List P3 → β) :
    tblK m x k = k (tbl m x) := by
  simp only [tblK, tblAK_eq, tbl]

@[expose] def tbP (m : Nat) (x : P6) : Tb := ⟨tbl m x.re, tbl m x.im⟩

theorem tbPK_eq {β : Sort _} (m : Nat) (x : P6) (k : Tb → β) :
    tbPK m x k = k (tbP m x) := by
  simp only [tbPK, tblK_eq, tbP]

@[expose] def addP (a : Option P3) (l : List P3) (i : Nat) : Option P3 :=
  bif Nat.beq i 0 then a else
    match a with
    | none => some (sel l i)
    | some a => some (ladd a (sel l i))

theorem addO_eq {β : Sort _} (a : Option P3) (l : List P3) (i : Nat)
    (k : Option P3 → β) : addO a l i k = k (addP a l i) := by
  unfold addO addP
  cases h : Nat.beq i 0 <;> cases a <;> simp only [Bool.cond_true, Bool.cond_false, laddK_eq]

@[expose] def linA : Option P3 → Option P3 → List (Tb × Nat) → P6
  | r, i, [] => ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l =>
    linA (addP (addP r t.r (a % 7)) t.i ((7 - a / 7 % 7) % 7))
      (addP (addP i t.r (a / 7 % 7)) t.i (a % 7)) l

theorem linAK_eq {β : Sort _} (r i : Option P3) (l : List (Tb × Nat)) (k : P6 → β) :
    linAK r i l k = k (linA r i l) := by
  induction l generalizing r i with
  | nil => rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    simp only [linAK, force_eq, addO_eq, ih, linA]

theorem linK_eq {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) :
    linK l k = k (linA none none l) :=
  linAK_eq none none l k

@[expose] def linCA : Option P3 → Option P3 → List (Tb × Nat) → P6
  | r, i, [] => ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l =>
    linCA (addP (addP r t.r (a % 7)) t.i (a / 7 % 7))
      (addP (addP i t.r (a / 7 % 7)) t.i ((7 - a % 7) % 7)) l

theorem linCAK_eq {β : Sort _} (r i : Option P3) (l : List (Tb × Nat)) (k : P6 → β) :
    linCAK r i l k = k (linCA r i l) := by
  induction l generalizing r i with
  | nil => rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    simp only [linCAK, force_eq, addO_eq, ih, linCA]

theorem linCK_eq {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) :
    linCK l k = k (linCA none none l) :=
  linCAK_eq none none l k

@[expose] def nsq (m : Nat) (x : P6) : List P3 :=
  [lmap m x.re (fun v => (7 - v * v % 7) % 7), lmap m x.im (fun v => (7 - v * v % 7) % 7)]

theorem nsqK_eq {β : Sort _} (m : Nat) (x : P6) (k : List P3 → β) :
    nsqK m x k = k (nsq m x) := by
  simp only [nsqK, lmapK_eq, nsq]

@[expose] def sqs (m s : Nat) (x : P6) : List P3 :=
  [lmap m x.re (fun v => s * (v * v) % 7), lmap m x.im (fun v => s * (v * v) % 7)]

theorem sqsK_eq {β : Sort _} (m s : Nat) (x : P6) (k : List P3 → β) :
    sqsK m s x k = k (sqs m s x) := by
  simp only [sqsK, lmapK_eq, sqs]

@[expose] def herUU (m : Nat) (u0 u1 u2 u4 u5 u6 : P6) : P3 :=
  sumP (sqs m 1 u0 ++ sqs m 1 u1 ++ sqs m 1 u2 ++ sqs m 1 u4 ++ sqs m 1 u5 ++ sqs m gfKappa u6)

theorem herUUK_eq {β : Sort _} (m : Nat) (u0 u1 u2 u4 u5 u6 : P6) (k : P3 → β) :
    herUUK m u0 u1 u2 u4 u5 u6 k = k (herUU m u0 u1 u2 u4 u5 u6) := by
  simp only [herUUK, sqsK_eq, sumK_eq, herUU]

@[expose] def vtxM (m : Nat) (T : Tabs) (u0 : P6) (h : P3) (c : N7) : Nat :=
  Nat.land (Nat.land (Nat.xor (lzero m h) m) (Nat.xor (lzero m (sumP (h :: nsq m u0))) m))
    (Nat.xor (lzero m (sumP ((addP none T.th (herN c c % 7)).toList ++
      nsq m (linCA none none (hcCoef T c))))) m)

theorem vtxMK_eq {β : Sort _} (m : Nat) (T : Tabs) (u0 : P6) (h : P3) (c : N7)
    (k : Nat → β) : vtxMK m T u0 h c k = k (vtxM m T u0 h c) := by
  simp only [vtxMK, nsqK_eq, sumK_eq, linCK_eq, force_eq, addO_eq, vtxM]

@[expose] def adjM (m : Nat) (T : Tabs) (v : N7) : Nat :=
  Nat.land (Nat.xor (lzero m (sumP ((addP none T.th (herN v v % 7)).toList ++
      nsq m (linA none none (herCoef T v))))) m)
    (Nat.land (lzero m (linA none none (bfCoef T v)).re) (lzero m (linA none none (bfCoef T v)).im))

theorem adjMK_eq {β : Sort _} (m : Nat) (T : Tabs) (v : N7) (k : Nat → β) :
    adjMK m T v k = k (adjM m T v) := by
  simp only [adjMK, linK_eq, force_eq, nsqK_eq, addO_eq, sumK_eq, adjM]

theorem laneVecK_eq {β : Sort _} (c : N7) (L : Nat) (k : N7 → β) :
    laneVecK c L k = k (laneVec c L) := by
  simp only [laneVecK, forceV7, force_eq]
  rfl

theorem stepL_cons (m : Nat) (T : Tabs) (V S : Nat) (c : N7) (L : Nat) (Ls : List Nat)
    (a : Nat) : stepL m T V S c (L :: Ls) a = bif S.testBit (L + 64) && decide (L < NL) then
      stepL m T V S c Ls (Nat.xor (Nat.lor a (Nat.land V (adjM m T (laneVec c L)))) (mix L))
    else none := by
  simp only [stepL, laneVecK_eq, adjMK_eq, force_eq]

@[expose] def tabS (f : Nat → Nat) (i : Nat) (acc : P6) : P6 :=
  ⟨⟨Nat.xor (Nat.lor acc.re.b0 (bif (f i % 7).testBit 0 then 2 ^ (i + 64) else 0)) (mix (6 * i)),
      Nat.xor (Nat.lor acc.re.b1 (bif (f i % 7).testBit 1 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 1)),
      Nat.xor (Nat.lor acc.re.b2 (bif (f i % 7).testBit 2 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 2))⟩,
    ⟨Nat.xor (Nat.lor acc.im.b0 (bif (f i / 7).testBit 0 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 3)),
      Nat.xor (Nat.lor acc.im.b1 (bif (f i / 7).testBit 1 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 4)),
      Nat.xor (Nat.lor acc.im.b2 (bif (f i / 7).testBit 2 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 5))⟩⟩

@[expose] def tab (f : Nat → Nat) : Nat → Nat → P6 → P6
  | _, 0, acc => acc
  | i, n + 1, acc => tab f (i + 1) n (tabS f i acc)

theorem tabK_eq {β : Sort _} (f : Nat → Nat) (i n : Nat) (acc : P6) (k : P6 → β) :
    tabK f i n acc k = k (tab f i n acc) := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih => simp only [tabK, force_eq, ih, tab, tabS]

theorem forceP6_eq {β : Sort _} (x : P6) (k : P6 → β) : forceP6 x k = k x := by
  simp only [forceP6, force_eq]

@[expose] def Tid : P6 := tab (fun k => k) 0 49 z6

@[expose] def Tsq : P6 := tab (fun k => gfMul k k) 0 49 z6

@[expose] def Tnp : P6 := tab (fun k => gfNeg (gfMul (k / 49) (k % 49))) 0 2401 z6

@[expose] def U1 : P6 := joinP (constP 1 117649 0) z6 z6 z6

@[expose] def U2 : P6 := joinP (mapP (fun p => spread p 2401 49) 6 Tid) (constP 1 2401 12) z6 z6

@[expose] def Ua : P6 := mapP (fun p => spread p 49 2401) 18 Tnp

@[expose] def Ub : P6 := mapP (fun p => rep p 49 2401) 24 Tsq

@[expose] def U4 : P6 := joinP ⟨ladd Ua.re Ub.re, ladd Ua.im Ub.im⟩
  (mapP (fun p => spread p 49 49) 30 Tid) (constP 1 49 36) z6

@[expose] def U5 : P6 := joinP (mapP (fun p => rep (spread p 49 49) 2401 49) 42 Tid)
  (mapP (fun p => rep p 49 49) 48 Tsq) Tid (constP 1 1 54)

@[expose] def U6 : P6 :=
  joinP (mapP (fun p => rep p 49 2401) 60 Tid) (mapP (fun p => rep p 49 49) 66 Tid) z6 z6

theorem withU_eq {β : Sort _} (k : P6 → P6 → P6 → P6 → P6 → β) :
    withU k = k U1 U2 U4 U5 U6 := by
  simp only [withU, tabK_eq, coordsK, forceP6_eq, laddK_eq]
  rfl

@[expose] def u0Of (c : N7) : P6 :=
  linA none none (b0Coef (tbP MM U1) (tbP MM U2) (tbP MM U4) (tbP MM U5) (tbP MM U6) c)

@[expose] def hOf (c : N7) : P3 := herUU MM (u0Of c) U1 U2 U4 U5 U6

@[expose] def tabsOf (c : N7) : Tabs :=
  ⟨tbP MM (u0Of c), tbP MM U1, tbP MM U2, tbP MM U4, tbP MM U5, tbP MM U6, tbl MM (hOf c)⟩

@[expose] def vOf (c : N7) : Nat := vtxM MM (tabsOf c) (u0Of c) (hOf c) c

theorem rowCore_eq (c : N7) (rootL : Nat) (lvls : List (List Nat)) :
    rowCore c rootL lvls = ((vOf c).testBit (rootL + 64) &&
      match runLv MM (tabsOf c) (vOf c) c (2 ^ (rootL + 64)) lvls with
      | none => false
      | some S => Nat.land (vOf c) (Nat.xor S MM) >>> 64 == 0) := by
  unfold rowCore
  simp only [force_eq, withU_eq, tbPK_eq, linK_eq, herUUK_eq, tblK_eq, vtxMK_eq]
  rfl

@[expose] def eqP3 (x y : P3) : Bool :=
  Nat.beq x.b0 y.b0 && Nat.beq x.b1 y.b1 && Nat.beq x.b2 y.b2

@[expose] def eqL3 : List P3 → List P3 → Bool
  | [], [] => true
  | x :: l, y :: m => eqP3 x y && eqL3 l m
  | _, _ => false

@[expose] def eqTb (t u : Tb) : Bool := eqL3 t.r u.r && eqL3 t.i u.i

@[expose] def eqTabs (T U : Tabs) : Bool :=
  eqTb T.t0 U.t0 && eqTb T.t1 U.t1 && eqTb T.t2 U.t2 && eqTb T.t4 U.t4 && eqTb T.t5 U.t5 &&
    eqTb T.t6 U.t6 && eqL3 T.th U.th

@[expose] def optB (o : Option Nat) (b : Nat) : Bool :=
  match o with
  | none => false
  | some a => Nat.beq a b

theorem eq_of_eqP3 {x y : P3} (h : eqP3 x y = true) : x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  simp only [eqP3, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  rw [Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]

theorem eq_of_eqL3 : ∀ {l m : List P3}, eqL3 l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqL3] at h
  | _ :: _, [], h => by simp [eqL3] at h
  | x :: l, y :: m, h => by
    simp only [eqL3, Bool.and_eq_true] at h
    rw [eq_of_eqP3 h.1, eq_of_eqL3 h.2]

theorem eq_of_eqTb {t u : Tb} (h : eqTb t u = true) : t = u := by
  obtain ⟨r, i⟩ := t
  obtain ⟨r', i'⟩ := u
  simp only [eqTb, Bool.and_eq_true] at h
  rw [eq_of_eqL3 h.1, eq_of_eqL3 h.2]

theorem eq_of_eqTabs {T U : Tabs} (h : eqTabs T U = true) : T = U := by
  obtain ⟨a0, a1, a2, a4, a5, a6, ah⟩ := T
  obtain ⟨b0, b1, b2, b4, b5, b6, bh⟩ := U
  simp only [eqTabs, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h4⟩, h5⟩, h6⟩, hh⟩ := h
  rw [eq_of_eqTb h0, eq_of_eqTb h1, eq_of_eqTb h2, eq_of_eqTb h4, eq_of_eqTb h5, eq_of_eqTb h6,
    eq_of_eqL3 hh]

theorem eq_of_optB {o : Option Nat} {b : Nat} (h : optB o b = true) : o = some b := by
  cases o with
  | none => simp [optB] at h
  | some a =>
    simp only [optB] at h
    rw [Nat.eq_of_beq_eq_true h]

theorem stepL_nil (m : Nat) (T : Tabs) (V S : Nat) (c : N7) (a : Nat) :
    stepL m T V S c [] a = some a := by
  simp only [stepL]

theorem stepL_append {m : Nat} {T : Tabs} {V S : Nat} {c : N7} :
    ∀ (l₁ l₂ : List Nat) (a b r : Nat), stepL m T V S c l₁ a = some b →
      stepL m T V S c l₂ b = some r → stepL m T V S c (l₁ ++ l₂) a = some r
  | [], _, a, b, _, h₁, h₂ => by
    rw [stepL_nil] at h₁
    cases h₁
    exact h₂
  | L :: l₁, l₂, a, b, r, h₁, h₂ => by
    rw [List.cons_append, stepL_cons]
    rw [stepL_cons] at h₁
    cases hc : (S.testBit (L + 64) && decide (L < NL))
    · rw [hc] at h₁
      simp at h₁
    · rw [hc] at h₁
      simp only [Bool.cond_true] at h₁ ⊢
      exact stepL_append l₁ l₂ _ b r h₁ h₂

theorem stepL_chunk {m : Nat} {T : Tabs} {V S : Nat} {c : N7} {Ls : List Nat} {d k d' a a' b : Nat}
    (hd : d + k = d') (h₁ : stepL m T V S c ((Ls.drop d).take k) a = some a')
    (h₂ : stepL m T V S c (Ls.drop d') a' = some b) : stepL m T V S c (Ls.drop d) a = some b := by
  rw [← List.take_append_drop k (Ls.drop d)]
  rw [List.drop_drop, hd]
  exact stepL_append _ _ a a' b h₁ h₂

theorem stepL_drop0 {m : Nat} {T : Tabs} {V S : Nat} {c : N7} {Ls : List Nat} {a b : Nat}
    (h : stepL m T V S c (Ls.drop 0) a = some b) : stepL m T V S c Ls a = some b := by
  rwa [List.drop_zero] at h

theorem runLv_cons {m : Nat} {T : Tabs} {V : Nat} {c : N7} {S S' : Nat} {Ls : List Nat}
    {rest : List (List Nat)} (h : stepL m T V S c Ls S = some S') :
    runLv m T V c S (Ls :: rest) = runLv m T V c S' rest := by
  simp only [runLv, h, force_eq]

theorem runLv3_of {m : Nat} {T : Tabs} {V : Nat} {c : N7} {lvls : List (List Nat)}
    {S0 S1 S2 S3 : Nat} (hl : Nat.beq lvls.length 3 = true)
    (h0 : stepL m T V S0 c (lvls.getD 0 []) S0 = some S1)
    (h1 : stepL m T V S1 c (lvls.getD 1 []) S1 = some S2)
    (h2 : stepL m T V S2 c (lvls.getD 2 []) S2 = some S3) :
    runLv m T V c S0 lvls = some S3 := by
  match lvls, Nat.eq_of_beq_eq_true hl with
  | [l0, l1, l2], _ =>
    change stepL m T V S0 c l0 S0 = some S1 at h0
    change stepL m T V S1 c l1 S1 = some S2 at h1
    change stepL m T V S2 c l2 S2 = some S3 at h2
    rw [runLv_cons h0, runLv_cons h1, runLv_cons h2]
    simp only [runLv]

theorem rowCore_of {c : N7} {rootL : Nat} {lvls : List (List Nat)} {T : Tabs} {V S0 S : Nat}
    (hT : eqTabs (tabsOf c) T = true) (hV : Nat.beq (vOf c) V = true)
    (hr : V.testBit (rootL + 64) = true) (h0 : Nat.beq (2 ^ (rootL + 64)) S0 = true)
    (hrun : runLv MM T V c S0 lvls = some S)
    (hf : (Nat.land V (Nat.xor S MM) >>> 64 == 0) = true) : rowCore c rootL lvls = true := by
  rw [rowCore_eq, eq_of_eqTabs hT, Nat.eq_of_beq_eq_true hV, hr, Nat.eq_of_beq_eq_true h0, hrun]
  exact hf

theorem forceV7_eq {β : Sort _} (v : N7) (k : N7 → β) : forceV7 v k = k v := by
  obtain ⟨a, b, c, d, e, f, g⟩ := v
  simp only [forceV7, force_eq]

theorem rowCheck_of {row : Array Nat} {rootL : Nat} {lvls : List (List Nat)}
    (hb : (((rowN row).x0 < 49 && (rowN row).x1 < 49 && (rowN row).x2 < 49 && (rowN row).x3 < 49 &&
      (rowN row).x4 < 49 && (rowN row).x5 < 49 && (rowN row).x6 < 49) &&
      (rowN row).x3 == 1 && isFFN (rowN row) && decide (lvls.length ≤ 6) &&
      decide (rootL < NL)) = true)
    (hc : rowCore (rowN row) rootL lvls = true) : rowCheck row rootL lvls = true := by
  unfold rowCheck
  rw [forceV7_eq]
  rw [hb, hc]
  rfl

@[expose] def packL3 : List P3 → Nat
  | [] => 0
  | x :: l => Nat.lor (Nat.lor x.b0 (Nat.shiftLeft x.b1 131072))
      (Nat.lor (Nat.shiftLeft x.b2 262144) (Nat.shiftLeft (packL3 l) 393216))

@[expose] def packTabs (T : Tabs) : Nat :=
  packL3 (T.t0.r ++ T.t0.i ++ T.t1.r ++ T.t1.i ++ T.t2.r ++ T.t2.i ++ T.t4.r ++ T.t4.i ++ T.t5.r ++
    T.t5.i ++ T.t6.r ++ T.t6.i ++ T.th)

open Lean in
meta def kwNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok (.lit (.natVal v)) => return v
  | .ok r => throwError "#q7_rec: not a literal: {r}"
  | .error _ => throwError "#q7_rec: kernel exception while reducing {e}"

open Lean in
meta def addDefE (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

open Lean in
meta def tabsE (v : Nat) : Expr := Id.run do
  let W := 131072
  let msk := (1 <<< W) - 1
  let p3 (i : Nat) : Expr :=
    mkApp3 (mkConst ``P3.mk) (mkRawNatLit ((v >>> (W * (3 * i))) &&& msk))
      (mkRawNatLit ((v >>> (W * (3 * i + 1))) &&& msk)) (mkRawNatLit ((v >>> (W * (3 * i + 2))) &&& msk))
  let p3T := mkConst ``P3
  let lst (j : Nat) : Expr := (List.range 7).foldr (fun t acc =>
    mkApp3 (mkConst ``List.cons [0]) p3T (p3 (7 * j + t)) acc) (mkApp (mkConst ``List.nil [0]) p3T)
  let tb (j : Nat) : Expr := mkApp2 (mkConst ``Tb.mk) (lst (2 * j)) (lst (2 * j + 1))
  return mkAppN (mkConst ``Tabs.mk) #[tb 0, tb 1, tb 2, tb 3, tb 4, tb 5, lst 12]

end CFSG.Certificates.Kernel.Q7Bits.Rec

open Lean Elab Command Meta CFSG.Certificates.Kernel.Q7Bits.Rec in
elab "#q7_rec " pre:ident c:term:max rootL:term:max lvls:term:max k:num : command => do
  let pre := pre.getId
  let k := k.getNat
  let nT := Lean.mkConst ``Nat
  let el (s : Term) (ty : Option Expr := none) : CommandElabM Expr := liftTermElabM do
    let e ← Term.elabTerm s ty
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let run (x : CoreM Unit) : CommandElabM Unit := liftCoreM <| withOptions (Elab.async.set · false) x
  let kw (s : Term) : CommandElabM Nat := do
    let e ← el s (some nT)
    liftTermElabM (kwNat e)
  let id (n : Name) : Ident := mkIdent (pre ++ n)
  let tv ← kw (← `(CFSG.Certificates.Kernel.Q7Bits.Rec.packTabs
    (CFSG.Certificates.Kernel.Q7Bits.Rec.tabsOf $c)))
  unless tv >>> (131072 * 273) == 0 do throwError "#q7_rec: tables do not fit"
  run <| addDefE (pre ++ `T) (Lean.mkConst ``CFSG.Certificates.Kernel.Q7Bits.Tabs) (tabsE tv)
  let v ← kw (← `(CFSG.Certificates.Kernel.Q7Bits.Rec.vOf $c))
  run <| addDefE (pre ++ `V) nT (mkRawNatLit v)
  let s0 ← kw (← `(2 ^ ($rootL + 64)))
  run <| addDefE (pre ++ `S0) nT (mkRawNatLit s0)
  let nl ← kw (← `(List.length $lvls))
  let mut S : Ident := id `S0
  for j in [0:nl] do
    let jl := Syntax.mkNumLit (toString j)
    let n ← kw (← `(List.length (List.getD $lvls $jl [])))
    let mut d := 0
    let mut a : Ident := S
    let mut m := 1
    while true do
      let dl := Syntax.mkNumLit (toString d)
      let kl := Syntax.mkNumLit (toString k)
      let chunk ← if d + k < n then `(List.take $kl (List.drop $dl (List.getD $lvls $jl [])))
        else `(List.drop $dl (List.getD $lvls $jl []))
      let v ← kw (← `(Option.getD (CFSG.Certificates.Kernel.Q7Bits.stepL
        CFSG.Certificates.Kernel.Q7Bits.MM $(id `T) $(id `V) $S $c $chunk $a) 0))
      let nm := Name.mkSimple s!"A{j}_{m}"
      run <| addDefE (pre ++ nm) nT (mkRawNatLit v)
      a := id nm
      m := m + 1
      d := d + k
      if d ≥ n then break
    S := a

end
