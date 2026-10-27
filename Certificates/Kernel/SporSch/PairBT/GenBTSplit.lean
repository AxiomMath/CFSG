module

public import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit
public meta import Certificates.Kernel.SporSch.Mathieu.GenBT
public import Certificates.Kernel.SporSch.Mathieu.GenBT

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.MBTS

open CFSG.KC.Tab CFSG.KS.RawGen

meta def parseChunks (s : String) (j : Nat) : Except String (Array (Nat × Nat × Nat)) := do
  let mut out := #[]
  for ln in s.splitOn "\n" do
    let ws := (ln.splitOn " ").filter (· ≠ "")
    if ws.isEmpty then continue
    let vs ← ws.mapM fun t => match t.toNat? with
      | some v => pure v
      | none => throw s!"parseChunks: bad token {t}"
    match vs with
    | [j', lo, len, v] => if j' == j then out := out.push (lo, len, v)
    | _ => throw s!"parseChunks: line of {vs.length} entries"
  return out

meta def chainArgs (Q : Name) (n w : Nat) (X : Expr) : Array Expr :=
  #[lit n, lit w, mkApp (mkConst ``CFSG.KS.mask) (lit w), mulE (lit n) (lit w),
    mkConst (Q ++ `BP), mkConst (Q ++ `LR), mkConst (Q ++ `TR), mkConst (Q ++ `TRI), X, X]

meta def btRE (Q : Name) (n w k : Nat) (X : Expr) (lo len : Nat) : Expr :=
  mkAppN (mkConst ``CFSG.KS.SporSch.MBT.btR) (chainArgs Q n w X ++ #[lit k, lit lo, lit len])

meta def chunkT (Q : Name) (n w k : Nat) (X : Expr) (c : Nat × Nat × Nat) : Expr :=
  isTrue (mkApp2 (mkConst ``Nat.beq) (btRE Q n w k X c.1 c.2.1) (lit c.2.2))

meta def chunksOf (H : Ident) (j : Nat) : CommandElabM (Array (Nat × Nat × Nat)) := do
  match parseChunks (← CFSG.KS.SporSch.MBTG.evalStr H) j with
  | .ok r => pure r
  | .error e => throwError e

end CFSG.KS.SporSch.MBTS

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MBTS in
elab "#kss_btchunks " pre:ident qq:ident nn:num ww:num kk:num xx:ident hId:ident jj:num
    i0:num i1:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let X := mkConst (← liftCoreM <| realizeGlobalConstNoOverload xx)
  let cs ← chunksOf hId jj.getNat
  withSync do
    for i in [i0.getNat:min i1.getNat cs.size] do
      CFSG.KS.RawGen.addThm (P ++ Name.mkSimple s!"c{i}")
        (chunkT Q nn.getNat ww.getNat kk.getNat X cs[i]!) reflBoolTrue

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MBTS in
elab "#kss_btjoin " pre:ident qq:ident nn:num ww:num kk:num xx:ident hId:ident jj:num :
    command => do
  let P := pre.getId
  let Q := qq.getId
  let X := mkConst (← liftCoreM <| realizeGlobalConstNoOverload xx)
  let n := nn.getNat
  let w := ww.getNat
  let k := kk.getNat
  let cs ← chunksOf hId jj.getNat
  if cs.isEmpty then throwError "#kss_btjoin: no chunks"
  for i in [0:cs.size - 1] do
    if cs[i]!.1 + cs[i]!.2.1 != cs[i + 1]!.1 then throwError "#kss_btjoin: chunks not adjacent"
  if cs[0]!.1 != 0 then throwError "#kss_btjoin: chunks not from 0"
  let refl := fun (v : Nat) => mkApp2 (mkConst ``Eq.refl [1]) natT (lit v)
  let ca := chainArgs Q n w X
  let last := cs[cs.size - 1]!
  let mut N := last.2.1
  let mut C := last.2.2
  let mut prf := mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) (btRE Q n w k X last.1 last.2.1)
    (lit last.2.2) (mkConst (P ++ Name.mkSimple s!"c{cs.size - 1}"))
  for i' in [0:cs.size - 1] do
    let i := cs.size - 2 - i'
    let (lo, a, v) := cs[i]!
    prf := mkAppN (mkConst ``CFSG.KS.SporSch.MBT.btR_join) (ca ++ #[lit k, lit lo, lit a, lit N,
      lit (a + N), lit v, lit C, lit (v + C), lit (lo + a), mkConst (P ++ Name.mkSimple s!"c{i}"),
      refl (lo + a), prf, refl (a + N), refl (v + C)])
    N := a + N
    C := v + C
  let hN := P ++ `hn
  let rc := mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (mkConst (Q ++ `LR)) (lit 0))
  let btK := mkAppN (mkConst ``CFSG.KS.SporSch.MBT.btK) (#[lit n, lit w,
    mkApp (mkConst ``CFSG.KS.mask) (lit w), mulE (lit n) (lit w), mkConst (Q ++ `BP), lit (k + 1),
    mkConst (Q ++ `LR), mkConst (Q ++ `TR), mkConst (Q ++ `TRI), X, X])
  withSync do
    CFSG.KS.RawGen.addThm hN (isTrue (mkApp2 (mkConst ``Nat.beq) rc (lit N))) reflBoolTrue
    CFSG.KS.RawGen.addThm (P ++ `hb) (mkApp3 (mkConst ``Eq [1]) natT btK (lit C))
      (mkAppN (mkConst ``CFSG.KS.SporSch.MBT.btK_of_btR) (ca ++ #[lit k, lit N, lit C,
        mkConst hN, prf]))

end
