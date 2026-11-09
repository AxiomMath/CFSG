module

public meta import Lean
public import Certificates.Data.Kernel.J3LocalK

public section

namespace CFSG.KC.J3Rec

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.M1F2 CFSG.KC.J3Loc

variable {V : Type}

@[expose] noncomputable def stepL (O : Ops Nat V) (R : List Nat) (op : Op) : List Nat :=
  Op.rec (motive := fun _ => List Nat) (fun i j t => R.set t (O.mul (getN R i) (getN R j)))
    (fun e i t => R.set t (powN O (Nat.succ e) (getN R i) e)) op

@[expose] noncomputable def runL (O : Ops Nat V) (prog : List Op) (R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun op _ ih R => ih (stepL O R op)) prog R

@[expose] noncomputable def eqNL (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (ih ys) (Nat.beq x y)) m) l

theorem eq_of_eqNL : ∀ {l m : List Nat}, eqNL l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    cases h
  | _ :: _, [], h => by
    change false = true at h
    cases h
  | x :: l, y :: m, h => by
    change Bool.rec (motive := fun _ => Bool) false (eqNL l m) (Nat.beq x y) = true at h
    cases hb : Nat.beq x y
    · rw [hb] at h
      change false = true at h
      cases h
    · rw [hb] at h
      change eqNL l m = true at h
      rw [Nat.eq_of_beq_eq_true hb, eq_of_eqNL h]

theorem forceB_eq (y : Nat) (k : Nat → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem forceL_eq : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    change forceB x (fun x' => forceL xs fun l => k (x' :: l)) = k (x :: xs)
    rw [forceB_eq, forceL_eq]

theorem runN_eq (O : Ops Nat V) : ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool),
    runN O prog R k = k (runL O prog R)
  | [], _, _ => rfl
  | op :: prog, R, k => by
    change stepN O R (fun R' => runN O prog R' k) op = k (runL O prog (stepL O R op))
    cases op with
    | mul i j t =>
      change forceB _ (fun a => forceL (R.set t a) _) = _
      rw [forceB_eq, forceL_eq, runN_eq O prog]
      rfl
    | pow e i t =>
      change forceB _ (fun a => forceL (R.set t a) _) = _
      rw [forceB_eq, forceL_eq, runN_eq O prog]
      rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem fullK_of {A B : Nat} {P : Nat → Nat} {N : Nat} {J : J3Cert} {Lv Ev : Nat}
    {Rv : List Nat} (hL : lanesP P N = Lv) (hE : onesL N = Ev)
    (hR : runL (opsF2K 80) J.prog (initN (opsF2K 80) A B J.nregs) = Rv)
    (hc : certN (opsF2K 80) Rv J.mcert = true) (hx : extraK J (P 0) Lv Ev Rv = true) :
    fullK A B P N J = true := by
  unfold fullK regsN
  rw [strictB_eq, strictB_eq, runN_eq, hL, hE, hR, hc, hx]
  rfl

theorem extraK_of {J : J3Cert} {root L E : Nat} {R : List Nat}
    (h1 : rangeK J = true)
    (h2 : (List.range 26).all (fun k =>
      Nat.beq (Nat.lor (movedL (tF (evalWN (opsF2K 80) R (basisW J.rb (k + 1)))) L E) (xsMask
        J.xs)) E) = true)
    (h3 : Nat.beq (colK (getN R J.rb.1) root) root = true)
    (h4 : (List.range 24).all (fun k =>
      (opsF2K 80).vne (colK (evalWN (opsF2K 80) R (basisW J.rb (k + 3))) root) root) = true)
    (h5 : (List.range 26).all (fun k =>
      !(opsF2K 80).eq (evalWN (opsF2K 80) R (basisW J.rb (k + 1))) (opsF2K 80).one) = true)
    (h6 : J.ss.all (fun s => Nat.beq (colK (getN R s.1) root) root) = true)
    (h7 : (J.cs.map (getN R)).zipIdx.all (fun p =>
      ((J.cs.map (getN R)).zip ((J.cs.map (getN R)).map fun X => powN (opsF2K 80) 3 X 2)).zipIdx.all
        fun q => Nat.beq p.2 q.2 || (!(opsF2K 80).eq p.1 q.1.1 && !(opsF2K 80).eq p.1 q.1.2)) =
          true)
    (h8 : (List.range 27).all (fun k => (List.range 8).all fun m =>
      !(opsF2K 80).eq (powN (opsF2K 80) 4 (evalWN (opsF2K 80) R (basisW J.rb k ++ hW J.rh (m +
        1))) 3)
        (opsF2K 80).one) = true)
    (h9 : Nat.beq J.ss.length J.cs.length = true) :
    extraK J root L E R = true := by
  simp only [extraK, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.and_self]

@[expose] noncomputable def packL (R : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 8192)) R

open Lean in
meta def kwNat (n : Name) : CoreM Nat := do
  match Kernel.whnf (← getEnv) {} (mkConst n) with
  | .ok (.lit (.natVal v)) => return v
  | .ok _ => throwError "#j3_kw: {n} does not reduce to a literal"
  | .error _ => throwError "#j3_kw: kernel exception while reducing {n}"

open Lean in
meta def addDefE (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

end CFSG.KC.J3Rec

open Lean Elab Command CFSG.KC.J3Rec in
elab "#j3_kw_nat " nm:ident src:ident : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let v ← kwNat (← realizeGlobalConstNoOverload src)
    addDefE nm.getId (mkConst ``Nat) (mkRawNatLit v)

open Lean Elab Command CFSG.KC.J3Rec in
elab "#j3_kw_list " nm:ident src:ident w:num n:num : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let v ← kwNat (← realizeGlobalConstNoOverload src)
    let w := w.getNat
    let n := n.getNat
    let m := (1 <<< w) - 1
    let xs := (List.range n).map fun i => (v >>> (w * i)) &&& m
    unless v >>> (w * n) == 0 do throwError "#j3_kw_list: more than {n} fields"
    let nT := mkConst ``Nat
    addDefE nm.getId (mkApp (mkConst ``List [0]) nT)
      (xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) nT (mkRawNatLit x) acc)
        (mkApp (mkConst ``List.nil [0]) nT))

end
