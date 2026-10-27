module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kqt_enumcodes " pre:ident nn:num cId:ident : command => do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload cId
  let C ← liftTermElabM <| unsafe evalConst (Array (List Nat) × Array Nat × Array Nat) nm
  let n := nn.getNat
  let codes := C.1.toList.map fun T => (T.take n).foldr (fun x acc => x + acc * 32) 0
  let listT := mkApp (mkConst ``List [0]) natT
  let val := codes.foldr (fun k acc => mkApp3 (mkConst ``List.cons [0]) natT (lit k) acc)
    (mkApp (mkConst ``List.nil [0]) natT)
  withSync do
    addDef pre.getId listT val

end
