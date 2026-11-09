module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.FactsVMeta
public meta import Certificates.Data.CFSGNative.LQTMul3
public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Kernel.LocalComp.FactsVMeta
public import Certificates.Kernel.LocalQT.Cmd

public section

open Lean Elab Command Meta

namespace CFSG.KC.LQT.CmdF

open CFSG.KC.LQT.Cmd

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
    let mut v3 : Array (Array CFSG.F3.Native.V) :=
      #[CFSG.F3.Native.rowsOf d strA, CFSG.F3.Native.rowsOf d strB, CFSG.F3.Native.idM d]
    for k in [3:ops.size] do
      let (a, b) := ops[k]!
      v3 := v3.push (Mul3.mulFR d v3[a]! v3[b]!)
    let tbl := Mul3.spreadTbl c.w
    let mut vals : Array Nat := #[]
    for k in [0:v3.size] do
      let x := if k == 2 then c.ONE else Mul3.toLane c.w d tbl v3[k]!
      vals := vals.push x
      addDef (pre ++ Name.mkSimple s!"V{k}") natE (bigLit x)
    addSel (pre ++ `V) (fun k => mkConst (pre ++ Name.mkSimple s!"V{k}")) vals.size
    addDef (pre ++ `N) natE (lit vals.size)
    for k in [3:ops.size] do
      let (a, b) := ops[k]!
      addDef (pre ++ Name.mkSimple s!"P{k}") natE (lit (a + (b <<< 20)))
    addSel (pre ++ `P) (fun k => if k < 3 then lit 0 else mkConst (pre ++ Name.mkSimple s!"P{k}"))
      ops.size
    let V := mkConst (pre ++ `V)
    let fld (f : Name) := mkApp (mkConst (``CFSG.KC.LQT.Lay ++ f)) lay
    let dS := mkAppN (mkConst ``HMul.hMul [0, 0, 0]) #[natE, natE, natE,
      mkApp2 (mkConst ``instHMul [0]) natE (mkConst ``instMulNat), fld `d, fld `S]
    let valid (k : Nat) := mkAppN (mkConst ``CFSG.KC.Ord.validM)
      #[fld `p, dS, fld `L, fld `H, mkApp V (lit k)]
    addTrue (pre ++ `vA) (valid 0)
    addTrue (pre ++ `vB) (valid 1)
    let oneTy := mkApp3 (mkConst ``Eq [1]) natE (mkApp V (lit 2))
      (mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay)
    addThm (pre ++ `one) oneTy (mkApp2 (mkConst ``Eq.refl [1]) natE (mkApp V (lit 2)))
    let O := D.outs.map fun r => regs[r]!
    let X := (O.map fun i => v3[i]!).toArray
    let r := O.length
    let unit (t : Nat) : CFSG.F3.Native.V := ⟨1 <<< t, 0⟩
    let mut W : Array Nat := #[0]
    for n in [1:3 ^ r] do
      match D.tests.find? (fun t => t < c.d && !(Mul3.digApp d X n (unit t)).beq (unit t)) with
      | some t => W := W.push t
      | none => throwError "no test vector moved by exponent code {n}"
    addSel (pre ++ `O) (fun i => lit O[i]!) r
    addSel (pre ++ `W) (fun n => lit W[n]!) W.size
    addTrue (pre ++ `elem) (mkAppN (mkConst ``CFSG.KC.LQT.elemOK)
      #[lay, V, lit vals.size, mkConst (pre ++ `O), mkConst (pre ++ `W), lit r])

end CFSG.KC.LQT.CmdF

end
