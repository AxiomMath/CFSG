module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Data.Kernel.BfsPin
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Data.TwinPerpSmSp1Wit
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

open Lean Elab Command

public section

namespace CFSG.KC.Q8WitGen

open CFSG.KC.Tab CFSG.KS.RawGen

elab "#q8w_data " pre:ident dId:ident ww:num : command => do
  let P := pre.getId
  let w := ww.getNat
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let D ← liftTermElabM <| unsafe evalConst Certificates.TwinPerpSmSp1.Q8WitData dN
  let n := D.syl.n
  let gens := CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qGens D.syl
  let (pts, edges) := CFSG.KC.BfsGen.search n w gens
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!)
  let keyOf := fun (a : Array Nat) => D.syl.qKeys.foldr (fun p acc => a[p]! + n * acc) 0
  let kv := pts.map keyOf
  let korder := (Array.range kv.size).qsort fun a b => kv[a]! < kv[b]!
  let cs := Certificates.TwinPerpSmSp1.cands D
  let Q := P ++ `Q
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (Q ++ `G) (gens.map (pack w))
    addDef (Q ++ `ng) natT (lit gens.size)
    addDef (Q ++ `N) natT (lit tv.size)
    addTree (Q ++ `T) tv
    addTree (Q ++ `E) ev
    addTree (Q ++ `S) order
    let ty := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.bfsK)
      #[lit n, lit w, mkConst (Q ++ `ng), mkConst (Q ++ `G), mkConst (Q ++ `N), mkConst (Q ++ `T),
        mkConst (Q ++ `E), mkConst (Q ++ `S)])
    CFSG.KC.addThmDecl <| { name := Q ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }
    addTree (Q ++ `SKT) korder
    addTree (P ++ `SQ) (pts.map fun a => pack w (comp n a a))
    addTree (P ++ `I) (pts.map fun a => pack w (inv n a))
    addTree (P ++ `PG) (D.syl.pg.map (pack w))
    addTree (P ++ `XG) (D.xg.map (pack w))
    addTree (P ++ `C) (cs.map (pack w))
    addTree (P ++ `CI) (cs.map fun a => pack w (inv n a))
    addDef (P ++ `nc) natT (lit cs.size)

end CFSG.KC.Q8WitGen

end
