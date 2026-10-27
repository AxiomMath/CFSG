module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.FactsVMeta
public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Kernel.LocalComp.FactsVMeta
public import Certificates.Kernel.LocalQT.Cmd

public section

open Lean Elab Command Meta

namespace CFSG.KC.LQT.CmdF

open CFSG.KC.LQT.Cmd

meta def mk (n : Nat) : Nat := (1 <<< n) - 1

meta def add3 (a b : Nat × Nat) : Nat × Nat :=
  let za := a.1 ||| a.2
  let zb := b.1 ||| b.2
  ((a.1 ^^^ (a.1 &&& zb)) ||| (b.1 ^^^ (b.1 &&& za)) ||| (a.2 &&& b.2),
   (a.2 ^^^ (a.2 &&& zb)) ||| (b.2 ^^^ (b.2 &&& za)) ||| (a.1 &&& b.1))

meta def mul3 (d E : Nat) (X Y : Nat × Nat) : Nat × Nat := Id.run do
  let m := mk d
  let mut acc : Nat × Nat := (0, 0)
  for j in [0:d] do
    let yp := (Y.1 >>> (d * j)) &&& m
    let ym := (Y.2 >>> (d * j)) &&& m
    if yp ||| ym != 0 then
      let sp := (X.1 >>> j) &&& E
      let sm := (X.2 >>> j) &&& E
      if sp ||| sm != 0 then
        acc := add3 acc ((sp * yp) ||| (sm * ym), (sp * ym) ||| (sm * yp))
  return acc

meta def spreadTbl (w : Nat) : Array Nat :=
  (Array.range 256).map fun x => Id.run do
    let mut r := 0
    for t in [0:8] do
      if (x >>> t) % 2 == 1 then r := r ||| (1 <<< (w * t))
    return r

meta partial def spread (w : Nat) (tbl : Array Nat) (x n : Nat) : Nat :=
  if x == 0 then 0
  else if n ≤ 8 then tbl[x]!
  else
    let h := if 16 ≤ n then 8 * (n / 16) else 8
    spread w tbl (x &&& mk h) h ||| (spread w tbl (x >>> h) (n - h) <<< (w * h))

meta def toLane (w nb : Nat) (tbl : Array Nat) (X : Nat × Nat) : Nat :=
  spread w tbl X.1 nb ||| (spread w tbl X.2 nb <<< 1)

meta partial def ofWords (ws : Array Nat) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi == lo + 1 then ws[lo]!
  else
    let mid := (lo + hi) / 2
    ofWords ws lo mid ||| (ofWords ws mid hi <<< (64 * (mid - lo)))

meta def decode3 (d : Nat) (s : String) : Nat × Nat := Id.run do
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let N := d * d
  let mut pw : Array Nat := #[]
  let mut mw : Array Nat := #[]
  let mut cp := 0
  let mut cm := 0
  let mut k := 0
  for ch in body do
    let n := ch.toNat
    if !(n == 32 || (9 ≤ n && n ≤ 13)) then
      if k < N then
        let e := (if 48 ≤ n && n ≤ 57 then n - 48 else 0) % 3
        if e == 1 then cp := cp ||| (1 <<< (k % 64))
        if e == 2 then cm := cm ||| (1 <<< (k % 64))
        if k % 64 == 63 then
          pw := pw.push cp
          mw := mw.push cm
          cp := 0
          cm := 0
      k := k + 1
  pw := pw.push cp
  mw := mw.push cm
  return (ofWords pw 0 pw.size, ofWords mw 0 mw.size)

meta def one3 (d : Nat) : Nat × Nat := (rep1 (d + 1) d, 0)

open CFSG.SectionRank.Native in
elab "#lqt_sr_vals " pre:ident dat:ident d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalData dat.getId
  withSync do
    let d := d.getNat
    let c := layOf 3 d
    unless c.S == c.w * d do throwError "row stride"
    let lay := mkConst (pre ++ `lay)
    addDef (pre ++ `lay) (mkConst ``CFSG.KC.LQT.Lay) c.expr
    addTrue (pre ++ `lay_ok) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ok) lay)
    let strA ← addChars (pre ++ `LA) sA.getId
    let strB ← addChars (pre ++ `LB) sB.getId
    let (ops, _, regs) := CFSG.KC.LocalComp.FactsVMeta.ssaIdx D.nregs D.prog
    let E := rep1 d d
    let tbl := spreadTbl c.w
    let nb := d * d
    let mut v3 : Array (Nat × Nat) := #[decode3 d strA, decode3 d strB, one3 d]
    for k in [3:ops.size] do
      let (a, b) := ops[k]!
      v3 := v3.push (mul3 d E v3[a]! v3[b]!)
    let mut vals : Array Nat := #[]
    for k in [0:v3.size] do
      let x := if k == 2 then c.ONE else toLane c.w nb tbl v3[k]!
      vals := vals.push x
      addDef (pre ++ Name.mkSimple s!"V{k}") natE (lit x)
    addSel (pre ++ `V) (fun k => mkConst (pre ++ Name.mkSimple s!"V{k}")) vals.size
    addDef (pre ++ `N) natE (lit vals.size)
    for k in [3:ops.size] do
      let (a, b) := ops[k]!
      addDef (pre ++ Name.mkSimple s!"P{k}") natE (lit (a + (b <<< 20)))
    addSel (pre ++ `P) (fun k => if k < 3 then lit 0 else mkConst (pre ++ Name.mkSimple s!"P{k}"))
      ops.size
    let V := mkConst (pre ++ `V)
    addTrue (pre ++ `decA) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 0))
      (mkConst (pre ++ `LA)))
    addTrue (pre ++ `decB) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 1))
      (mkConst (pre ++ `LB)))
    let oneTy := mkApp3 (mkConst ``Eq [1]) natE (mkApp V (lit 2))
      (mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay)
    addThm (pre ++ `one) oneTy (mkApp2 (mkConst ``Eq.refl [1]) natE (mkApp V (lit 2)))
    let O := D.outs.map fun r => regs[r]!
    let X := (O.map fun i => vals[i]!).toArray
    let r := O.length
    let mut W : Array Nat := #[0]
    for n in [1:3 ^ r] do
      match D.tests.find? (fun t => t < c.d && c.digApp 3 X n (c.unit t) != c.unit t) with
      | some t => W := W.push t
      | none => throwError "no test vector moved by exponent code {n}"
    addSel (pre ++ `O) (fun i => lit O[i]!) r
    addSel (pre ++ `W) (fun n => lit W[n]!) W.size
    addTrue (pre ++ `elem) (mkAppN (mkConst ``CFSG.KC.LQT.elemOK)
      #[lay, V, lit vals.size, mkConst (pre ++ `O), mkConst (pre ++ `W), lit r])

end CFSG.KC.LQT.CmdF

end
