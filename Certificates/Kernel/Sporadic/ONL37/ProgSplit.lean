module

public import Certificates.Kernel.Sporadic.ONL37.Seg
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

open Lean Elab Command Term in
meta def kcRegsCmd (id : Ident) (t : Term) (W N : Nat) (prev : Option Ident) (K : Nat) :
    CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ id.getId
  let v ← liftTermElabM do
    let e ← elabTerm t (some (Lean.mkConst ``Nat))
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then throwError "#kc_regs: the term is not closed"
    CFSG.KC.Benes.kNat (toString id.getId) e
  let mask := (1 <<< W) - 1
  let natE := Lean.mkConst ``Nat
  let ns ← getCurrNamespace
  let prevN : Option Name := prev.map fun p => ns ++ p.getId
  liftCoreM do
    let mut kept : Array Expr := #[]
    if let some pn := prevN then
      let some pv := (← getConstInfo pn).value? | throwError "#kc_regs: {pn} has no value"
      let mut cur := pv
      for _ in [0:K] do
        unless cur.isAppOfArity ``List.cons 3 do throwError "#kc_regs: {pn} is too short"
        kept := kept.push (cur.getArg! 1)
        cur := cur.getArg! 2
    for i in [kept.size:N] do
      CFSG.KC.Load.addDef (base.appendAfter s!"_{i}") natE (mkRawNatLit ((v >>> (W * i)) &&& mask)) true
    let elt := fun i => if h : i < kept.size then kept[i] else Lean.mkConst (base.appendAfter s!"_{i}")
    let lst := (List.range N).foldr (fun i acc => mkApp3 (Lean.mkConst ``List.cons [0]) natE (elt i) acc)
      (mkApp (Lean.mkConst ``List.nil [0]) natE)
    CFSG.KC.Load.addDef base (mkApp (Lean.mkConst ``List [0]) natE) lst true

elab "#kc_regs " id:ident " := " t:term " width " w:num " count " n:num : command =>
  kcRegsCmd id t w.getNat n.getNat none 0

elab "#kc_regs_keep " id:ident " := " t:term " width " w:num " count " n:num " keep " p:ident
    k:num : command =>
  kcRegsCmd id t w.getNat n.getNat (some p) k.getNat

namespace CertificateChecks.KernelSpor.ONL37

@[expose] noncomputable def packR (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

section
variable {mul : Nat → Nat → Nat} {vld : Nat → Bool} {one : Nat} {VI : Nat → Nat}
variable {mul : Nat → Nat → Nat} {vld : Nat → Bool} {one : Nat} {VI : Nat → Nat}

@[expose] noncomputable def runSt (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat) (VI : Nat → Nat) :
    List CFSG.RankThree.Native.ONTriple.SOp → List Nat × Bool → List Nat × Bool :=
  List.rec (motive := fun _ => List Nat × Bool → List Nat × Bool) (fun st => st)
    (fun o _ ih st => ih (Prod.rec (motive := fun _ => List Nat × Bool) (fun R ok => (R, ok))
      (CFSG.KS.ONC.stepS mul vld one VI st o)))

theorem runS_eq (k : List Nat × Bool → Bool) :
    ∀ (P : List CFSG.RankThree.Native.ONTriple.SOp) (st : List Nat × Bool), CFSG.KS.ONC.runS mul vld one VI k P st = k (runSt mul vld one VI P st)
  | [], _ => rfl
  | o :: P, st => by
    show Prod.rec (motive := fun _ => Bool) (fun R ok => CFSG.KS.ONC.runS mul vld one VI k P (R, ok))
        (CFSG.KS.ONC.stepS mul vld one VI st o) =
      k (runSt mul vld one VI P (Prod.rec (motive := fun _ => List Nat × Bool) (fun R ok => (R, ok))
        (CFSG.KS.ONC.stepS mul vld one VI st o)))
    generalize CFSG.KS.ONC.stepS mul vld one VI st o = s
    cases s
    exact runS_eq k P _

theorem runS_append (fin : List Nat × Bool → Bool) :
    ∀ (P Q : List CFSG.RankThree.Native.ONTriple.SOp) (st : List Nat × Bool),
      CFSG.KS.ONC.runS mul vld one VI fin (P ++ Q) st = CFSG.KS.ONC.runS mul vld one VI (fun s => CFSG.KS.ONC.runS mul vld one VI fin Q s) P st
  | [], _, _ => rfl
  | o :: P, Q, st => by
    show Prod.rec (motive := fun _ => Bool) (fun R ok => CFSG.KS.ONC.runS mul vld one VI fin (P ++ Q) (R, ok))
        (CFSG.KS.ONC.stepS mul vld one VI st o) =
      Prod.rec (motive := fun _ => Bool)
        (fun R ok => CFSG.KS.ONC.runS mul vld one VI (fun s => CFSG.KS.ONC.runS mul vld one VI fin Q s) P (R, ok))
        (CFSG.KS.ONC.stepS mul vld one VI st o)
    generalize CFSG.KS.ONC.stepS mul vld one VI st o = s
    cases s
    exact runS_append fin P Q _

@[expose] noncomputable def listEqN : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y r _ => bAnd(Nat.beq x y, ih r)) b)

theorem listEqN_spec : ∀ {a b : List Nat}, listEqN a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [listEqN])
  | _ :: _, [], h => absurd h (by simp [listEqN])
  | x :: a, y :: b, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (listEqN a b) (Nat.beq x y) = true := h
    cases hb : Nat.beq x y
    · rw [hb] at h'; exact absurd h' (by simp)
    · rw [hb] at h'
      rw [Nat.eq_of_beq_eq_true hb, listEqN_spec h']

@[expose] noncomputable def stOK (st : List Nat × Bool) (R : List Nat) : Bool := bAnd(st.2, listEqN st.1 R)

theorem stOK_spec {st : List Nat × Bool} {R : List Nat} (h : stOK st R = true) : st = (R, true) := by
  obtain ⟨R', b⟩ := st
  have h' : Bool.rec (motive := fun _ => Bool) false (listEqN R' R) b = true := h
  cases b
  · exact absurd h' (by simp)
  · rw [listEqN_spec h']

theorem runS_seg {fin : List Nat × Bool → Bool} (P : List CFSG.RankThree.Native.ONTriple.SOp) (m n k : Nat) (hk : m + n = k)
    {st : List Nat × Bool} (R : List Nat)
    (h1 : CFSG.KS.ONC.runS mul vld one VI (fun s => stOK s R) (List.take n (List.drop m P)) st = true)
    (h2 : CFSG.KS.ONC.runS mul vld one VI fin (List.drop k P) (R, true) = true) :
    CFSG.KS.ONC.runS mul vld one VI fin (List.drop m P) st = true := by
  rw [runS_eq] at h1
  rw [← List.take_append_drop n (List.drop m P), runS_append, runS_eq, stOK_spec h1, List.drop_drop,
    hk]
  exact h2
end

section
open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def sopA (L0 H0 CM0 RM0 ONE0 : Nat)
    (m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat) (v3 : Nat → Nat → Nat → Bool)
    (init : List Nat) (VI : Nat → Nat) (fin : List Nat × Bool → Bool) (prog : List SOp) : Bool :=
  strictB L0 fun L => strictB H0 fun H => strictB CM0 fun cm => strictB RM0 fun rm =>
  strictB ONE0 fun one =>
    bAnd(CFSG.KS.ONC.initS (m3 L H cm rm) (v3 L H) one VI init init.length,
      CFSG.KS.ONC.runS (m3 L H cm rm) (v3 L H) one VI fin prog (init, true))

end

theorem sopK_eqA (init : List Nat) (VI : Nat → Nat) (fin : List Nat × Bool → Bool)
    (prog : List CFSG.RankThree.Native.ONTriple.SOp) :
    CFSG.KS.ONC.sopK init VI fin prog =
      sopA CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM CFSG.KS.ONC.ONE
        CFSG.KS.ONC.mul3 CFSG.KS.ONC.vld3 init VI fin prog := rfl

theorem sopA_of {L0 H0 CM0 RM0 ONE0 : Nat} {m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat}
    {v3 : Nat → Nat → Nat → Bool} {init : List Nat} {VI : Nat → Nat} {fin : List Nat × Bool → Bool}
    {prog : List CFSG.RankThree.Native.ONTriple.SOp}
    (hi : CFSG.KS.ONC.initS (m3 L0 H0 CM0 RM0) (v3 L0 H0) ONE0 VI init init.length = true)
    (hr : CFSG.KS.ONC.runS (m3 L0 H0 CM0 RM0) (v3 L0 H0) ONE0 VI fin prog (init, true) = true) :
    sopA L0 H0 CM0 RM0 ONE0 m3 v3 init VI fin prog = true := by
  unfold sopA
  simp only [strictB_eq']
  rw [hi, hr]

theorem sopK_of {init : List Nat} {VI : Nat → Nat} {fin : List Nat × Bool → Bool}
    {prog : List CFSG.RankThree.Native.ONTriple.SOp}
    (hi : CFSG.KS.ONC.initS
      (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
      (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VI init init.length = true)
    (hr : CFSG.KS.ONC.runS
      (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
      (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VI fin prog (init, true) = true) :
    CFSG.KS.ONC.sopK init VI fin prog = true :=
  (sopK_eqA init VI fin prog).trans (sopA_of hi hr)

end CertificateChecks.KernelSpor.ONL37

end
