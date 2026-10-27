module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnapsChunks
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunks

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.KC.LaySnapsChunks

public section

namespace CFSG.KC.LaySnapsFrom

elab "#lay_snaps_from " pre:ident p:num d:num s0:ident cs:ident : command => do
  let pre := pre.getId
  let S₀ ← liftCoreM <| do
    (← listOfE (← valueOf (← realizeGlobalConstNoOverload s0))).mapM natOfE
  let chs ← liftCoreM <| do listOfE (← valueOf (← realizeGlobalConstNoOverload cs))
  let c := layOf p.getNat d.getNat
  withSync do
    let listT := mkApp (mkConst ``List [0]) natE
    let mut S : List Nat := S₀
    addDef (pre ++ `S0) listT (natList S)
    let mut i := 0
    for ch in chs do
      let (nE, rest) ← pairOfE ch
      let (opsE, outE) ← pairOfE rest
      let ops ← (← listOfE opsE).mapM fun o => do (← listOfE o).mapM natOfE
      let out ← (← listOfE outE).mapM natOfE
      S ← runChunk c S (← natOfE nE) ops out
      i := i + 1
      addDef (pre ++ Name.mkSimple s!"S{i}") listT (natList S)
    let sl := (List.range (i + 1)).foldr
      (fun k acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{k}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl

end CFSG.KC.LaySnapsFrom

end
