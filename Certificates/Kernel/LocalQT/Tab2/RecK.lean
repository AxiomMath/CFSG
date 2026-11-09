module

public meta import Lean
public import Certificates.Data.Kernel.LocalQT.Tab2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab

open Lean Elab Command Meta

public section

namespace CFSG.KD.LQT.T2Rec

open CFSG.KC.Ord CFSG.KC.LQT.T2 CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def eqLB (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) m) l

@[expose] noncomputable def eqPB (l : List (Nat × Nat)) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (andB (Nat.beq x.1 y.1) (Nat.beq x.2 y.2)) (ih ys)) m) l

@[expose] noncomputable def someB (o : Option (List (Nat × Nat))) (m : List (Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun l => eqPB l m) o

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · change false = true at h
    cases h
  · exact ⟨rfl, h⟩

theorem eq_of_eqLB : ∀ {l m : List Nat}, eqLB l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    cases h
  | _ :: _, [], h => by
    change false = true at h
    cases h
  | x :: l, y :: m, h => by
    change andB (Nat.beq x y) (eqLB l m) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    rw [Nat.eq_of_beq_eq_true h1, eq_of_eqLB h2]

theorem eq_of_eqPB : ∀ {l m : List (Nat × Nat)}, eqPB l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    cases h
  | _ :: _, [], h => by
    change false = true at h
    cases h
  | (a, b) :: l, (c, d) :: m, h => by
    change andB (andB (Nat.beq a c) (Nat.beq b d)) (eqPB l m) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨h3, h4⟩ := andB_true h1
    rw [Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, eq_of_eqPB h2]

theorem eq_of_someB : ∀ {o : Option (List (Nat × Nat))} {m : List (Nat × Nat)},
    someB o m = true → o = some m
  | none, _, h => by
    change false = true at h
    cases h
  | some l, _, h => by
    change eqPB l _ = true at h
    rw [eq_of_eqPB h]

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem checkK_of {n : Nat} {ta tb : List Nat} {order : Nat} {clS : List Char}
    {hGensW : List (List Nat)} {hS : List Char} {pGensW : List (List Nat)} {pS : List Char}
    {eaGens ebGens : List (List Nat)} {gaW gbW : List Nat} {cp hp pp : List (Nat × Nat)}
    {A B : Nat} {cl Hl Pl Ea Eb : List Nat}
    (h1 : parseK clS = some cp) (h2 : parseK hS = some hp) (h3 : parseK pS = some pp)
    (hA : codeT ta = A) (hB : codeT tb = B)
    (hcl : bfsQ (fun x g => mul n (mul n g x) (inv n g)) (one n) [A, B, inv n A, inv n B] A cp = cl)
    (hHl : bfsQ (mul n) (one n) (List.map (wordK n A B) hGensW) (one n) hp = Hl)
    (hPl : bfsQ (mul n) (one n) (List.map (wordK n A B) pGensW) (one n) pp = Pl)
    (hEa : spanK n (List.map codeT eaGens) = Ea) (hEb : spanK n (List.map codeT ebGens) = Eb)
    (h : allBs
      [monoK cp, monoK hp, monoK pp,
       tabOK n ta, tabOK n tb, allT eaGens (tabOK n), allT ebGens (tabOK n),
       distinctS cl, distinctS Hl, Nat.beq (Nat.mul (lenL cl) (lenL Hl)) order,
       allL Hl (fun h => comm n h A),
       distinctL Pl, Nat.beq (lenL Pl) 128, Nat.beq (Nat.mod (Nat.div order 128) 2) 1,
       closedT n Pl, closedT n Ea, closedT n Eb, eokT n Pl Ea, eokT n Pl Eb,
       memL A Ea, memL A Eb, anyL Ea (fun t => notB (memL t Eb)),
       selfCentT n Hl Ea, selfCentT n Hl Eb,
       witT n (wordK n A B gaW) Ea Eb, witT n (wordK n A B gbW) Eb Ea,
       classT n Pl Ea Eb] = true) :
    checkK n ta tb order clS hGensW hS pGensW pS eaGens ebGens gaW gbW = true := by
  unfold checkK
  rw [h1, h2, h3]
  dsimp only
  rw [hA, letB_eq, hB, letB_eq]
  rw [hcl, hHl, hPl, hEa, hEb]
  exact h

meta def natW (e : Expr) : MetaM Nat := do
  if let some n ← (evalNat (← instantiateMVars e)).run then return n
  let e' ← whnf e
  if let some n ← (evalNat e').run then return n
  throwError "#lqt_t2_rec: not a natural number literal: {e}"

meta partial def listW (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return e.appFn!.appArg! :: (← listW e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return []
  else
    throwError "#lqt_t2_rec: not a list: {e}"

meta def natsW (e : Expr) : MetaM (List Nat) := do (← listW e).mapM natW

meta def strOf (n : Name) : MetaM String := do
  let some v := (← getConstInfo n).value? | throwError "#lqt_t2_rec: {n} has no value"
  match v.consumeMData with
  | .lit (.strVal s) => return s
  | _ => throwError "#lqt_t2_rec: {n} is not a string literal"

meta def pairsN (s : String) : List (Nat × Nat) :=
  ((s.splitOn " ").filter fun t => !t.isEmpty).map fun t =>
    match t.splitOn "," with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, 0)

meta def imgN (s i : Nat) : Nat := (s >>> (5 * i)) &&& 31
meta def mulN (n s t : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (imgN s (imgN t i) <<< (5 * i))) 0
meta def invN (n s : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (i <<< (5 * imgN s i))) 0
meta def oneN (n : Nat) : Nat := (List.range n).foldl (fun acc i => acc + (i <<< (5 * i))) 0
meta def codeN (t : List Nat) : Nat := t.foldr (fun x acc => x + 32 * acc) 0
meta def letN (n A B l : Nat) : Nat :=
  if l = 0 then A else if l = 1 then B else if l = 2 then invN n A else invN n B
meta def wordN (n A B : Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc l => mulN n acc (letN n A B l)) (oneN n)
meta def bfsN (op : Nat → Nat → Nat) (d : Nat) (gens : List Nat) (start : Nat)
    (par : List (Nat × Nat)) : List Nat := Id.run do
  let mut E : Array Nat := #[start]
  for (i, g) in par do
    E := E.push (op (E.getD i start) (gens.getD g d))
  return E.toList
meta def spanN (n : Nat) (l : List Nat) : List Nat :=
  l.foldr (fun e S => S ++ S.map (mulN n e)) [oneN n]

meta def natsE (xs : List Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit x) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

meta def pairsE (xs : List (Nat × Nat)) : Expr :=
  let nT := mkConst ``Nat
  let pT := mkApp2 (mkConst ``Prod [0, 0]) nT nT
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) pT
      (mkApp4 (mkConst ``Prod.mk [0, 0]) nT nT (mkRawNatLit x.1) (mkRawNatLit x.2)) acc)
    (mkApp (mkConst ``List.nil [0]) pT)

meta def addDefE (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

end CFSG.KD.LQT.T2Rec

open CFSG.KD.LQT.T2Rec in
elab "#lqt_t2_rec " pre:ident n:num D:ident clS:ident hS:ident pS:ident : command => do
  let pre := pre.getId
  let n := n.getNat
  let Dn ← liftCoreM <| realizeGlobalConstNoOverload D
  let (cs, hs, ps) ← liftCoreM <| do
    return (← realizeGlobalConstNoOverload clS, ← realizeGlobalConstNoOverload hS,
      ← realizeGlobalConstNoOverload pS)
  let defs ← liftTermElabM do
    let fld (f : Name) : Expr :=
      mkApp (mkConst (``CFSG.QuasithinUnique.Unc25G2.M2x.Dat ++ f)) (mkConst Dn)
    let ta ← natsW (fld `ta)
    let tb ← natsW (fld `tb)
    let hG ← (← listW (fld `hGensW)).mapM fun e => natsW e
    let pG ← (← listW (fld `pGensW)).mapM fun e => natsW e
    let eaG ← (← listW (fld `eaGens)).mapM fun e => natsW e
    let ebG ← (← listW (fld `ebGens)).mapM fun e => natsW e
    let cp := pairsN (← strOf cs)
    let hp := pairsN (← strOf hs)
    let pp := pairsN (← strOf ps)
    let A := codeN ta
    let B := codeN tb
    let cl := bfsN (fun x g => mulN n (mulN n g x) (invN n g)) (oneN n)
      [A, B, invN n A, invN n B] A cp
    let Hl := bfsN (mulN n) (oneN n) (hG.map (wordN n A B)) (oneN n) hp
    let Pl := bfsN (mulN n) (oneN n) (pG.map (wordN n A B)) (oneN n) pp
    let Ea := spanN n (eaG.map codeN)
    let Eb := spanN n (ebG.map codeN)
    let lpT :=
      mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))
    let lnT := mkApp (mkConst ``List [0]) (mkConst ``Nat)
    return [(`CPr, lpT, pairsE cp), (`HPr, lpT, pairsE hp), (`PPr, lpT, pairsE pp),
      (`Ar, mkConst ``Nat, mkRawNatLit A), (`Br, mkConst ``Nat, mkRawNatLit B),
      (`CLr, lnT, natsE cl), (`HLr, lnT, natsE Hl), (`PLr, lnT, natsE Pl),
      (`EAr, lnT, natsE Ea), (`EBr, lnT, natsE Eb)]
  liftCoreM <| withOptions (Elab.async.set · false) do
    for (nm, ty, v) in defs do
      addDefE (pre ++ nm) ty v

end
