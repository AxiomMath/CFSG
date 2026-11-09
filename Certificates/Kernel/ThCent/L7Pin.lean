module

public import Certificates.Kernel.ThCent.LDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

namespace CFSG.KD.ThCent.L

open Lean CFSG.SectionRank.Native CFSG.KC.Eval

meta def mulM (c rm A B : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:248] do
    acc := Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
      (Nat.mul (Nat.land (Nat.shiftRight B (k * 256)) rm) c))
  return acc

meta def powM (c rm ONE M e nb : Nat) : Nat := Id.run do
  let mut acc := ONE
  for i in [0:nb] do
    let sq := mulM c rm acc acc
    acc := if (e >>> (nb - 1 - i)) &&& 1 == 1 then mulM c rm sq M else sq
  return acc

meta def snap7Step : Step := fun args => do
  let #[.nat c, .nat rm, .nat one, .nat a, .nat b, .nat k] := args
    | throw "snap7Step: expected c rm ONE A B k"
  let mut R : Array Nat := ((Array.replicate 43 one).set! 0 a).set! 1 b
  let mut outs : Array (Name × Val) := #[]
  let mut refs : Array Val := #[]
  let mut n := 0
  for op in CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 do
    match op with
    | .mul x y t =>
      unless x < 43 && y < 43 && t < 43 do throw "snap7Step: register past 42"
      R := R.set! t (mulM c rm R[x]! R[y]!)
    | .pow e x t =>
      unless x < 43 && t < 43 do throw "snap7Step: register past 42"
      R := R.set! t (powM c rm one R[x]! e 6)
    n := n + 1
    if n % k == 0 then
      let nm := Name.mkSimple s!"S{refs.size}"
      outs := outs.push (nm, .list (R.map .nat))
      refs := refs.push (.ref nm)
  if n % k != 0 then
    let nm := Name.mkSimple s!"S{refs.size}"
    outs := outs.push (nm, .list (R.map .nat))
    refs := refs.push (.ref nm)
  return outs.push (`SL, .list refs)

set_option maxRecDepth 400000 in
#kc_eval CFSG.KD.ThCent.L P7 CFSG.KD.ThCent.L.snap7Step CFSG.KD.ThS.c CFSG.KD.ThS.rm
  CFSG.KD.ThS.ONE CFSG.KD.ThS.Rf_1 CFSG.KD.ThS.Rf_2 50

end CFSG.KD.ThCent.L

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

theorem strictF_eq7 {α : Sort _} (y : Nat) (k : Nat → α) : strictF y k = k y := by
  cases y <;> rfl

theorem runPk_mul7 (c rm ONE i j k : Nat) (p : List Op) (R : Nat → Nat) :
    runPk c rm ONE (.mul i j k :: p) R = runPk c rm ONE p (updN R k (mulB c rm (R i) (R j))) :=
  strictF_eq7 (mulB c rm (R i) (R j)) fun v => runPk c rm ONE p (updN R k v)

theorem runPk_pow7 (c rm ONE e i k : Nat) (p : List Op) (R : Nat → Nat) :
    runPk c rm ONE (.pow e i k :: p) R =
      runPk c rm ONE p (updN R k (powB c rm ONE (R i) e (nat_lit 6))) :=
  strictF_eq7 (powB c rm ONE (R i) e (nat_lit 6)) fun v => runPk c rm ONE p (updN R k v)

theorem beq_ne7 {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem runPk_append7 (c rm ONE : Nat) (p q : List Op) (R : Nat → Nat) :
    runPk c rm ONE (p ++ q) R = runPk c rm ONE q (runPk c rm ONE p R) := by
  induction p generalizing R with
  | nil => rfl
  | cons op p ih =>
    cases op with
    | mul i j k => rw [List.cons_append, runPk_mul7, runPk_mul7, ih]
    | pow e i k => rw [List.cons_append, runPk_pow7, runPk_pow7, ih]

theorem runPk_out7 (c rm ONE n : Nat) (p : List Op) (hp : p.all (Op.lt n) = true) (r : Nat)
    (hr : n ≤ r) (R : Nat → Nat) : runPk c rm ONE p R r = R r := by
  induction p generalizing R with
  | nil => rfl
  | cons op p ih =>
    rw [List.all_cons, Bool.and_eq_true] at hp
    cases op with
    | mul i j k =>
      have hk : k < n := by simp [Op.lt] at hp; omega
      rw [runPk_mul7, ih hp.2]
      have : Nat.beq r k = false := beq_ne7 (by omega)
      simp only [updN, this]
    | pow e i k =>
      have hk : k < n := by simp [Op.lt] at hp; omega
      rw [runPk_pow7, ih hp.2]
      have : Nat.beq r k = false := beq_ne7 (by omega)
      simp only [updN, this]

@[expose] noncomputable def snapR7 (S : List Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) ThS.ONE (S.getD r 0) (Nat.blt r 43)

@[expose] noncomputable def st7 : Nat → Nat → Nat
  | 0 => initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE
  | i + 1 => snapR7 (P7.SL.getD i [])

@[expose] noncomputable def seg7 (i : Nat) : List Op := (prog7.drop (i * 50)).take 50

@[expose] noncomputable def seg7OK (i : Nat) : Bool :=
  (seg7 i).all (Op.lt 43) &&
    (List.range 43).all fun r => Nat.beq (runPk ThS.c ThS.rm ThS.ONE (seg7 i) (st7 i) r) (st7 (i + 1) r)

theorem st7_out (i r : Nat) (hr : 43 ≤ r) : st7 i r = ThS.ONE := by
  have hb : Nat.blt r 43 = false := by
    cases h : Nat.blt r 43
    · rfl
    · rw [Nat.blt_eq] at h
      omega
  cases i with
  | zero =>
    have h0 : Nat.beq r 0 = false := beq_ne7 (by omega)
    have h1 : Nat.beq r 1 = false := beq_ne7 (by omega)
    simp only [st7, initPk, h0, h1]
  | succ i => simp only [st7, snapR7, hb]

theorem seg7_run {i : Nat} (h : seg7OK i = true) :
    runPk ThS.c ThS.rm ThS.ONE (seg7 i) (st7 i) = st7 (i + 1) := by
  rw [seg7OK, Bool.and_eq_true] at h
  funext r
  by_cases hr : r < 43
  · exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h.2 r (List.mem_range.2 hr))
  · rw [runPk_out7 _ _ _ 43 _ h.1 r (by omega), st7_out _ _ (by omega), st7_out _ _ (by omega)]

theorem seg7_0 : seg7OK 0 = true := by quickRfl
theorem seg7_1 : seg7OK 1 = true := by quickRfl
theorem seg7_2 : seg7OK 2 = true := by quickRfl
theorem seg7_3 : seg7OK 3 = true := by quickRfl
theorem seg7_4 : seg7OK 4 = true := by quickRfl
theorem seg7_5 : seg7OK 5 = true := by quickRfl
theorem seg7_6 : seg7OK 6 = true := by quickRfl
theorem seg7_7 : seg7OK 7 = true := by quickRfl
theorem seg7_8 : seg7OK 8 = true := by quickRfl
theorem seg7_9 : seg7OK 9 = true := by quickRfl
theorem seg7_10 : seg7OK 10 = true := by quickRfl

theorem prog7_len : prog7.length ≤ 11 * 50 := by decide +kernel

theorem run7 : runPk ThS.c ThS.rm ThS.ONE prog7 (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) = st7 11 := by
  have hs : ∀ i < 11, seg7OK i = true := by
    intro i hi
    match i, hi with
    | 0, _ => exact seg7_0
    | 1, _ => exact seg7_1
    | 2, _ => exact seg7_2
    | 3, _ => exact seg7_3
    | 4, _ => exact seg7_4
    | 5, _ => exact seg7_5
    | 6, _ => exact seg7_6
    | 7, _ => exact seg7_7
    | 8, _ => exact seg7_8
    | 9, _ => exact seg7_9
    | 10, _ => exact seg7_10
  have key : ∀ j ≤ 11, runPk ThS.c ThS.rm ThS.ONE (prog7.take (j * 50)) (st7 0) = st7 j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, runPk_append7, ih (by omega)]
      exact seg7_run (hs j (by omega))
  rw [← List.take_of_length_le prog7_len]
  exact key 11 (Nat.le_refl 11)

theorem pin7_2 : pin7 2 = true := by rw [pin7, run7]; quickRfl
theorem pin7_3 : pin7 3 = true := by rw [pin7, run7]; quickRfl
theorem pin7_24 : pin7 24 = true := by rw [pin7, run7]; quickRfl
theorem pin7_25 : pin7 25 = true := by rw [pin7, run7]; quickRfl
theorem pin7_31 : pin7 31 = true := by rw [pin7, run7]; quickRfl
theorem pin7_34 : pin7 34 = true := by rw [pin7, run7]; quickRfl
theorem pin7_39 : pin7 39 = true := by rw [pin7, run7]; quickRfl
theorem pin7_40 : pin7 40 = true := by rw [pin7, run7]; quickRfl
theorem pin7_41 : pin7 41 = true := by rw [pin7, run7]; quickRfl
theorem pin7_42 : pin7 42 = true := by rw [pin7, run7]; quickRfl

end CFSG.KD.ThCent.L

end
