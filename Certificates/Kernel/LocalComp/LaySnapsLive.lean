module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.HarnessGz
public import Certificates.Data.Kernel.NC2L
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
public import Certificates.Kernel.LocalComp.LaySnaps

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

public section

namespace CFSG.KC.LaySnapsLive

meta def powB (c : LayV) (X e : Nat) : Nat := Id.run do
  let mut r := c.ONE
  let mut b := X
  let mut e := e
  while 0 < e do
    if e % 2 == 1 then r := c.mul r b
    e := e / 2
    if 0 < e then b := c.mul b b
  return r

structure Chunk where
  n : Nat
  prog : Array (Nat × Nat × Nat × Nat)
  out : Array Nat

meta def natJ (j : Json) : Except String Nat := do
  let .num x := j | throw s!"expected a natural number, got {j}"
  unless x.exponent == 0 && x.mantissa ≥ 0 do throw s!"expected a natural number, got {j}"
  return x.mantissa.toNat

meta def chunkJ (j : Json) : Except String Chunk := do
  let n ← natJ (← j.getObjVal? "n")
  let prog ← (← (← j.getObjVal? "prog").getArr?).mapM fun o => do
    let o ← o.getArr?
    unless o.size == 4 do throw s!"an instruction has {o.size} entries"
    return (← natJ o[0]!, ← natJ o[1]!, ← natJ o[2]!, ← natJ o[3]!)
  let out ← (← (← j.getObjVal? "out").getArr?).mapM natJ
  return { n, prog, out }

meta def runChunk (c : LayV) (C : Chunk) (R : Array Nat) : Except String (Array Nat) := do
  let mut R := R ++ Array.replicate (C.n - R.size) c.ONE
  for (e, i, j, k) in C.prog do
    unless i < R.size && k < R.size && (e != 0 || j < R.size) do
      throw s!"instruction {(e, i, j, k)} out of range ({R.size} registers)"
    unless e < 65536 do throw s!"exponent {e} not below 2^16"
    let v := if e == 0 then c.mul R[i]! R[j]! else powB c R[i]! e
    R := R.set! k v
  for r in C.out do
    unless r < R.size do throw s!"output register {r} out of range ({R.size} registers)"
  return C.out.map (R[·]!)

meta def opE (o : Nat × Nat × Nat × Nat) : Expr :=
  let (e, i, j, k) := o
  if e == 0 then mkApp3 (mkConst ``Op.mul) (lit i) (lit j) (lit k)
  else mkApp3 (mkConst ``Op.pow) (lit e) (lit i) (lit k)

meta def listE (α : Expr) (es : List Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) α e acc) (mkApp (mkConst ``List.nil [0]) α)

end CFSG.KC.LaySnapsLive

open CFSG.KC.Gz CFSG.KC.LaySnaps CFSG.KC.LaySnapsLive in
elab "#lay_snaps_live " pre:ident p:num d:num a:ident b:ident path:str size:num hash:num :
    command => do
  let pre := pre.getId
  let A ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload a)
  let B ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload b)
  let bytes ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? bytes | throwError "#lay_snaps_live: {path.getString} is not UTF-8"
  let chunks ← match do (← (← (← Json.parse s).getObjVal? "chunks").getArr?).mapM chunkJ with
    | .ok cs => pure cs
    | .error e => throwError "#lay_snaps_live: {path.getString}: {e}"
  let c := layOf p.getNat d.getNat
  let chunkT := mkConst ``CFSG.KC.NC2L.LiveChunk
  let listT := mkApp (mkConst ``List [0]) natE
  let m := chunks.size
  withSync do
    let mut R : Array Nat := #[A, B]
    addDef (pre ++ `S0) listT (natList R.toList)
    let mut i : Nat := 0
    for C in chunks do
      addDef (pre ++ Name.mkSimple s!"C{i}") chunkT
        (mkApp3 (mkConst ``CFSG.KC.NC2L.LiveChunk.mk) (lit C.n)
          (listE (mkConst ``Op) (C.prog.toList.map opE)) (natList C.out.toList))
      match runChunk c C R with
      | .ok R' => R := R'
      | .error e => throwError "#lay_snaps_live: chunk {i}: {e}"
      i := i + 1
      addDef (pre ++ Name.mkSimple s!"S{i}") listT (natList R.toList)
    addDef (pre ++ `CL) (mkApp (mkConst ``List [0]) chunkT)
      (listE chunkT ((List.range m).map fun i => mkConst (pre ++ Name.mkSimple s!"C{i}")))
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT)
      (listE listT ((List.range (m + 1)).map fun i => mkConst (pre ++ Name.mkSimple s!"S{i}")))
    addDef (pre ++ `m) natE (lit m)

end
