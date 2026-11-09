module

public meta import Lean

open Lean Elab Command

public section

namespace CertificateChecks.KernelLyS0.Cmd

meta def natOf (n : Name) : CoreM Nat := do
  let some v := (← getConstInfo n).value? | throwError "#lys0_envs: {n} has no value"
  match v.consumeMData with
  | .lit (.natVal k) => return k
  | _ => throwError "#lys0_envs: {n} is not a literal"

meta def strOf (n : Name) : CoreM String := do
  let some v := (← getConstInfo n).value? | throwError "#lys0_envs: {n} has no value"
  match v.consumeMData with
  | .lit (.strVal s) => return s
  | _ => throwError "#lys0_envs: {n} is not a string literal"

meta def mulRN (p w S d T L H CM RM A B : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    acc := acc + ((A >>> (w * k)) &&& CM) * ((B >>> (S * k)) &&& RM)
  for i in [0:T + 1] do
    let c := p <<< (T - i)
    acc := acc - ((((acc ||| H) - c * L) &&& H) >>> (w - 1)) * c
  return acc

meta def pairE (k v : Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit k) (mkRawNatLit v)

meta def envE (xs : List (Nat × Nat)) : Expr :=
  let pT := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) pT (pairE x.1 x.2) acc)
    (mkApp (mkConst ``List.nil [0]) pT)

meta def addDefE (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

end CertificateChecks.KernelLyS0.Cmd

open CertificateChecks.KernelLyS0.Cmd in
elab "#lys0_envs " pre:ident "[" cuts:num,* "]" : command => do
  let pre := pre.getId
  let cuts := cuts.getElems.toList.map (·.getNat)
  liftCoreM <| withOptions (Elab.async.set · false) do
    let A ← natOf `CertificateChecks.KernelSporSch.LyBS.A
    let B ← natOf `CertificateChecks.KernelSporSch.LyBS.B
    let L ← natOf `CFSG.KD.OrdLy.L
    let H ← natOf `CFSG.KD.OrdLy.H
    let CM ← natOf `CFSG.KD.OrdLy.CM
    let RM ← natOf `CFSG.KD.OrdLy.RM
    let s ← strOf `CFSG.Sporadic.Ly.S0.opsStr
    let nums := (((s.replace "\n" " ").splitOn " ").filter fun t => !t.isEmpty).toArray.map
      String.toNat!
    let n := nums.size / 2
    let mut R : Array Nat := #[A, B]
    for t in [0:n] do
      R := R.push (mulRN 5 12 1332 111 8 L H CM RM R[nums[2 * t]!]! R[nums[2 * t + 1]!]!)
    let mut j := 1
    for c in cuts do
      let mut live : Array Nat := #[]
      for t in [c:n] do
        for x in [nums[2 * t]!, nums[2 * t + 1]!] do
          if x < c + 2 && !live.contains x then live := live.push x
      let sorted := live.qsort (· < ·)
      let pT := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
      addDefE (pre ++ Name.mkSimple s!"E{j}") (mkApp (mkConst ``List [0]) pT)
        (envE (sorted.toList.map fun k => (k, R[k]!)))
      j := j + 1

end
