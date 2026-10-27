module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalQT.Pipe.Twin
public import Certificates.Kernel.LocalQT.Pipe.Twin

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_codes " pre:ident tId:ident ww:num : command => do
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  withSync <| addTreeT (pre.getId ++ `TF) (T.map (pk ww.getNat))

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_wcp " pre:ident tId:ident wId:ident ss:num rr:num ww:num : command => do
  let s := ss.getNat
  let R := rr.getNat
  let w := ww.getNat
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let T ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  let wits ← liftTermElabM <| unsafe evalConst (List (List Nat × List Nat × Nat)) wN
  let words := wits.toArray.flatMap fun wt => #[wt.1.toArray, wt.2.1.toArray]
  let n := T[0]!.size
  let mut cps : Array Nat := #[]
  for wd in words do
    let mut acc := Array.range n
    for c in [0:R] do
      cps := cps.push (pk w acc)
      for k in [c * s:min (c * s + s) wd.size] do
        let l := if wd[k]! == 0 then T[0]! else T[1]!
        acc := l.map fun q => acc[q]!
  withSync <| addTreeT (pre.getId ++ `CP) cps

meta def mulIdxM (g : Nat) (par cl : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, k => k
  | f + 1, i, k =>
    if i = 0 then k
    else
      let j := ((List.range g).find? fun j => cl[par[i]! * (2 * g) + j]! == i).getD 0
      cl[mulIdxM g par cl f par[i]! k * (2 * g) + j]!

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_zs " pre:ident cId:ident gg:num nn:num ww:num : command => do
  let P := pre.getId
  let g := gg.getNat
  let n := nn.getNat
  let w := ww.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) cN
  let N := C.1.size
  let mul := mulIdxM g C.2.1 C.2.2 N
  let gs := (List.range g).map fun j => C.2.2[j]!
  let step := fun (Z : Array Nat) => (Array.range N).filter fun x =>
    gs.all fun s => Z.any fun z => mul x s == mul z (mul s x)
  let Z1 := step #[0]
  let Z2 := step Z1
  let Z3 := step Z2
  let Qc := (Array.range N).filter fun x => Z3.all fun y => mul x y == mul y x
  let listT := mkApp (mkConst ``List [0]) natT
  withSync do
    addDef (P ++ `Z1L) listT (natListE Z1)
    addDef (P ++ `Z2L) listT (natListE Z2)
    addDef (P ++ `Z3L) listT (natListE Z3)
    addDef (P ++ `QcL) listT (natListE Qc)
    addTreeT (P ++ `RC) (C.1.map fun l => pk w (l.take n).toArray)

end
