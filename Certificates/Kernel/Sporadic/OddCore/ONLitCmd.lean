module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public import CFSG.Sporadic.ONOddCore.LiftPayload
public import CFSG.Certificates.Kernel.Common.Tab
public meta import Mathlib.Init
public import Mathlib.Init

open Lean Elab Command

public section

namespace CertificateChecks.KernelSpor.ONLit

open CFSG.KC.Tab CFSG.Sporadic.ONOddCore

meta def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def natsE (xs : List Nat) : Expr := listE natT (xs.map lit)

meta def arrE (a : Array Nat) : Expr := mkApp2 (mkConst ``List.toArray [0]) natT (natsE a.toList)

meta def wordsE (ws : List (List Nat)) : Expr :=
  listE (mkApp (mkConst ``List [0]) natT) (ws.map natsE)

meta def liftE (e : LiftEntry) : Expr := mkApp2 (mkConst ``LiftEntry.mk) (lit e.power) (wordsE e.words)

meta def recE (r : QuotRecord) : Expr :=
  mkApp5 (mkConst ``QuotRecord.mk) (lit r.diag) (lit r.field) (lit r.graph)
    (listE (mkApp (mkConst ``Array [0]) natT) (r.images.map arrE))
    (listE (mkConst ``LiftEntry) (r.lifts.map liftE))

meta def certE (c : LocalCert) : Expr :=
  mkApp2 (mkConst ``LocalCert.mk) (listE (mkApp (mkConst ``Array [0]) natT) (c.quotGens.map arrE))
    (listE (mkConst ``QuotRecord) (c.records.map recE))

meta def candE : Cand → Expr
  | .lift i => mkApp (mkConst ``Cand.lift) (lit i)
  | .rel w w' => mkApp2 (mkConst ``Cand.rel) (natsE w) (natsE w')

meta def liftDataE (d : LiftData) : Expr :=
  let lnT := mkApp (mkConst ``List [0]) natT
  mkApp3 (mkConst ``LiftData.mk) (natsE d.qWord)
    (listE (mkApp (mkConst ``List [0]) lnT) (d.lw.map wordsE))
    (listE (mkApp (mkConst ``List [0]) (mkConst ``Cand)) (d.cands.map fun cs =>
      listE (mkConst ``Cand) (cs.map candE)))

end CertificateChecks.KernelSpor.ONLit

open CertificateChecks.KernelSpor.ONLit CFSG.KC.Tab CFSG.Sporadic.ONOddCore in
elab "#kon_certlit " pre:ident cId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let c ← liftTermElabM <| unsafe evalConst LocalCert cN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId (mkConst ``LocalCert) (certE c)

open CertificateChecks.KernelSpor.ONLit CFSG.KC.Tab CFSG.Sporadic.ONOddCore in
elab "#kon_liftlit " pre:ident dId:ident : command => do
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let d ← liftTermElabM <| unsafe evalConst LiftData dN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId (mkConst ``LiftData) (liftDataE d)

end
