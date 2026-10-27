module

public import Certificates.Kernel.Sporadic.ON.Gen
public meta import Certificates.Kernel.Sporadic.ON.Gen
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ONGen in
elab "#kon_tables " tId:ident ps:ident+ : command => do
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let t ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) tN
  if t.size != ps.size then
    throwError "#kon_tables: {t.size} tables for {ps.size} names"
  withSync do
    for i in [0:ps.size] do
      addTree ps[i]!.getId (leaves 18 6 t[i]!)

end
