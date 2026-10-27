module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.BfsLSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen in
elab "#kbfsl " pre:ident mm:num gId:ident lId:ident : command => do
  let P := pre.getId
  let m := mm.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let L ← liftTermElabM <| unsafe evalConst (Array Nat) lN
  let cnt := L.size
  let none32 := 4294967295
  let mut pos : Array Nat := Array.replicate m none32
  for k in [0:cnt] do
    pos := pos.set! L[k]! k
  let mut par : Array Nat := Array.replicate cnt 0
  let mut lab : Array Nat := Array.replicate cnt 0
  let mut seen : Array Bool := (Array.replicate cnt false).set! 0 true
  for j in [0:cnt] do
    for s in [0:gens.size] do
      let y := (gens[s]!)[L[j]!]!
      if y < m then
        let q := pos[y]!
        if q < cnt && !seen[q]! then
          seen := seen.set! q true
          par := par.set! q j
          lab := lab.set! q s
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PTS) (rows32 L)
    addTree (P ++ `POS) (rows32 pos)
    addTree (P ++ `PAR) (rows32 par)
    addTree (P ++ `LAB) (rows32 lab)
    addDef (P ++ `cnt) natT (lit cnt)

end
