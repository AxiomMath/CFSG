module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.LocalQT.Pipe.Twin
public import Certificates.Kernel.LocalQT.Pipe.Twin

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin in
elab "#kqt_pc " pre:ident cId:ident gg:num ww:num : command => do
  let P := pre.getId
  let g := gg.getNat
  let w := ww.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) cN
  let cl := (Array.range C.2.2.size).map fun i => if i % (2 * g) < g then C.2.2[i]! else 0
  let rows := fun (a : Array Nat) => (Array.range ((a.size + 63) / 64)).map fun r =>
    pk w ((Array.range 64).map fun j => a.getD (64 * r + j) 0)
  withSync do
    addDef (P ++ `PK) natT (lit (pk w C.2.1))
    addDef (P ++ `CK) natT (lit (pk w cl))
    addTreeT (P ++ `PT) (rows C.2.1)
    addTreeT (P ++ `CT) (rows cl)

end
