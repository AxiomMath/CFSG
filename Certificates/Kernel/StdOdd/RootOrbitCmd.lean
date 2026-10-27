module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.StdOdd.RootOrbitTwin
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertOrbit
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.LieType.Chevalley.C2E6StandardFixedData
public meta import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import Certificates.Kernel.StdOdd.RootOrbitTwin

public section

namespace CFSG.KC.StdOdd.Orbit

open Lean Elab Command CFSG.KC.Tab CFSG.Monster.Existence.StdOdd.CertNative

meta def natListE (xs : List Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

elab "#e6_orbit_data " pre:ident : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let m := 22
  let t0 ← IO.monoMsNow
  let AB := CFSG.LieType.Chevalley.C2E6Std.MatrixModel.nativeAB
  let c := produce AB.1 AB.2 e7
  let n := c.pts.size
  let t1 ← IO.monoMsNow
  let keys := sortedKeys c.pts
  let t2 ← IO.monoMsNow
  let rank := ranksOf keys c.idx
  let W := 1 <<< m
  let dstA := movesOf W rank c.nbA
  let dstB := movesOf W rank c.nbB
  let r := rank[0]!
  let t3 ← IO.monoMsNow
  let PL := planesOf keys n
  let t4 ← IO.monoMsNow
  let ds := benesDs m
  let MA := bytesToNats (routeBenes m dstA)
  let MB := bytesToNats (routeBenes m dstB)
  let t5 ← IO.monoMsNow
  let some RS := reachSets ds MA MB r n
    | throwError "#e6_orbit_data: the search stops before reaching every point"
  let t6 ← IO.monoMsNow
  logInfo m!"#e6_orbit_data: n = {n}, r = {r}, D = {RS.size - 1}; ms: produce {t1 - t0}, sort \
    {t2 - t1}, ranks {t3 - t2}, planes {t4 - t3}, route {t5 - t4}, search {t6 - t5}"
  let lnT := mkApp (mkConst ``List [0]) natT
  withSync do
    addDef (P ++ `PL) lnT (natListE PL.toList)
    addDef (P ++ `DS) lnT (natListE ds)
    addDef (P ++ `MA) lnT (natListE MA)
    addDef (P ++ `MB) lnT (natListE MB)
    addDef (P ++ `RS) lnT (natListE RS.toList)
    addDef (P ++ `r) natT (lit r)
    addDef (P ++ `D) natT (lit (RS.size - 1))

end CFSG.KC.StdOdd.Orbit

end
