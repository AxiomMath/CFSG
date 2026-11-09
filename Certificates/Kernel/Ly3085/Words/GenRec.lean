module

public meta import Lean
public import Certificates.Data.Kernel.LyOmega.Words

open Lean Elab Command Meta

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord

@[expose] noncomputable def pairB (p q : Nat × Nat) : Bool :=
  andB (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)

theorem eq_of_pairB {p q : Nat × Nat} (h : pairB p q = true) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  change andB (Nat.beq a c) (Nat.beq b d) = true at h
  cases h1 : Nat.beq a c
  · rw [h1] at h
    change false = true at h
    cases h
  · rw [h1] at h
    change Nat.beq b d = true at h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h]

theorem slpVals_of (C : BConsts) (A B Bi : Nat) (ws : List (List Int)) (V : List (Nat × Nat))
    (hl : V.length = ws.length)
    (h : ∀ j < ws.length, wordLanes C A B Bi (V.take j) j (ws.getD j []) = V.getD j (0, 0)) :
    slpVals C A B Bi ws = V := by
  have key : ∀ m k, k + m = ws.length → slpRun C A B Bi (V.take k) (ws.drop k) = V := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      rw [List.drop_length, ← hl, List.take_length]
      rfl
    | succ m ih =>
      intro k hk
      have hk' : k < ws.length := by omega
      have hV : k < V.length := by omega
      rw [List.drop_eq_getElem_cons hk']
      change slpRun C A B Bi (V.take k ++ [wordLanes C A B Bi (V.take k) (V.take k).length ws[k]])
        (ws.drop (k + 1)) = V
      have e1 : (V.take k).length = k := by rw [List.length_take]; omega
      have e2 : ws.getD k [] = ws[k] := by simp [List.getD_eq_getElem?_getD, hk']
      have e3 : V.getD k (0, 0) = V[k] := by simp [List.getD_eq_getElem?_getD, hV]
      have hw := h k hk'
      rw [e2, e3] at hw
      rw [e1, hw, List.take_append_getElem hV]
      exact ih (k + 1) (by omega)
  exact key ws.length 0 (by omega)

meta def natW (e : Expr) : MetaM Nat := do
  if let some n ← (evalNat (← instantiateMVars e)).run then return n
  let e' ← whnf e
  if let some n ← (evalNat e').run then return n
  throwError "#lyom_genvals: not a natural number literal: {e}"

meta def intW (e : Expr) : MetaM Int := do
  let e ← whnf e
  if e.isAppOfArity ``Int.ofNat 1 then return Int.ofNat (← natW e.appArg!)
  else if e.isAppOfArity ``Int.negSucc 1 then return Int.negSucc (← natW e.appArg!)
  else throwError "#lyom_genvals: not an integer literal: {e}"

meta partial def listW (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return e.appFn!.appArg! :: (← listW e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return []
  else
    throwError "#lyom_genvals: not a list: {e}"

meta def natOf (n : Name) : MetaM Nat := do
  let some v := (← getConstInfo n).value? | throwError "#lyom_genvals: {n} has no value"
  match v.consumeMData with
  | .lit (.natVal k) => return k
  | _ => throwError "#lyom_genvals: {n} is not a literal"

meta def mulRN (p w S d T L H CM RM A B : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    acc := acc + ((A >>> (w * k)) &&& CM) * ((B >>> (S * k)) &&& RM)
  for i in [0:T + 1] do
    let c := p <<< (T - i)
    acc := acc - ((((acc ||| H) - c * L) &&& H) >>> (w - 1)) * c
  return acc

meta def pairsE (xs : List (Nat × Nat)) : Expr :=
  let nT := mkConst ``Nat
  let pT := mkApp2 (mkConst ``Prod [0, 0]) nT nT
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) pT
      (mkApp4 (mkConst ``Prod.mk [0, 0]) nT nT (mkRawNatLit x.1) (mkRawNatLit x.2)) acc)
    (mkApp (mkConst ``List.nil [0]) pT)

end CFSG.KD.LyOm

open CFSG.KD.LyOm in
elab "#lyom_genvals " nm:ident : command => do
  let nm := nm.getId
  let vals ← liftTermElabM do
    let A ← natOf `CertificateChecks.KernelSporSch.LyBS.A
    let B ← natOf `CertificateChecks.KernelSporSch.LyBS.B
    let Bi ← natOf `CertificateChecks.KernelSporSch.LyBS.B4
    let LF ← natOf `CFSG.KD.LyOm.fLF
    let HF ← natOf `CFSG.KD.LyOm.fHF
    let CMF ← natOf `CFSG.KD.LyOm.fCMF
    let ONE ← natOf `CFSG.KD.LyOm.fONEF
    let rmB := (1 <<< 1332) - 1
    let mul := fun X Y => mulRN 5 12 1332 111 8 LF HF CMF rmB X Y
    let ws ← (← listW (mkConst `CFSG.KD.LyOm.genExt)).mapM fun w => do
      (← listW w).mapM fun z => intW z
    let mut V : Array (Nat × Nat) := #[]
    for w in ws do
      let j := V.size
      let mut p := (ONE, ONE)
      for z in w do
        let q : Nat × Nat :=
          if z = 1 then (A, A) else if z = -1 then (A, A) else if z = 2 then (B, Bi)
          else if z.natAbs ≤ 2 then (Bi, B)
          else if z.natAbs - 3 < j then
            (if 0 < z then V.getD (z.natAbs - 3) (ONE, ONE)
              else ((V.getD (z.natAbs - 3) (ONE, ONE)).2, (V.getD (z.natAbs - 3) (ONE, ONE)).1))
          else (ONE, ONE)
        p := (mul p.1 q.1, mul q.2 p.2)
      V := V.push p
    return V.toList
  let nT := mkConst ``Nat
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := nm, levelParams := [],
        type := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) nT nT),
        value := pairsE vals, hints := .regular 0, safety := .safe }

end
