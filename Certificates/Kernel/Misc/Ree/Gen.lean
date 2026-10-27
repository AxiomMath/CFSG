module

public import CFSG.Certificates.Kernel.Misc.ReeSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

namespace CFSG.KC.Misc.ReeGen

meta def enc (p n : Nat) : Nat := Id.run do
  let mut x := 0
  for i in [0:200] do
    let c := ((p >>> i) &&& 1) + 2 * ((n >>> i) &&& 1)
    x := x ||| (c <<< (32 * i))
  return x

meta def rep (L v : Nat) : Nat := Id.run do
  let mut x := 0
  for i in [0:L] do
    x := x ||| (v <<< (32 * i))
  return x

structure Fld where
  k : Nat
  G : Nat
  M15 : Nat
  ML : Nat

meta def Fld.red3 (c : Fld) (x : Nat) : Nat := x - 3 * (((x * 43691) >>> 17) &&& c.M15)

meta def Fld.norm (c : Fld) (N : Nat) : Nat := Id.run do
  let mut N := N
  for _ in [0:2 * c.k] do
    let H := N >>> (32 * c.k)
    if H == 0 then return N
    N := c.red3 ((N &&& c.ML) + H * c.G)
  return N

meta def Fld.mul (c : Fld) (a b : Nat) : Nat := c.norm (c.red3 (a * b))

meta def Fld.pow (c : Fld) (a e : Nat) : Nat := Id.run do
  let mut acc := 1
  for t in [0:e.log2 + 1] do
    let j := e.log2 - t
    acc := c.mul acc acc
    if (e >>> j) &&& 1 == 1 then acc := c.mul acc a
  return acc

meta def Fld.add (c : Fld) (x y : Nat) : Nat := c.red3 (x + y)

meta def Fld.sub (c : Fld) (x y : Nat) : Nat := c.red3 (x + 2 * y)

meta def addThm (n : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := n, levelParams := [], type := ty, value := v }

meta def modInv (x m : Nat) : Nat := Id.run do
  let mut r0 : Int := x
  let mut r1 : Int := m
  let mut s0 : Int := 1
  let mut s1 : Int := 0
  for _ in [0:4 * (m.log2 + 2)] do
    if r1 == 0 then break
    let q := r0 / r1
    (r0, r1) := (r1, r0 - q * r1)
    (s0, s1) := (s1, s0 - q * s1)
  return (s0 % (m : Int)).toNat

meta def caseData (c : Fld) (b : Nat) : Option (Nat × Nat × Nat) :=
  let k := c.k
  let q := 3 ^ k
  if Nat.gcd b k != 1 || 2 * b % k == 1 || Nat.gcd (3 ^ b + 2) (q - 1) != 1 then none else
  let s := modInv (3 ^ b + 2) (q - 1)
  let h := (q - 1) / 2
  let a0 := modInv ((3 ^ b + 1) / 2) h
  let a := if a0 % 2 == 0 then a0 else a0 + h
  let e := 3 ^ b + 1
  let z := c.pow ((1 <<< 32) + 1) s
  let y := c.pow ((1 <<< 32) + 2) s
  let u := c.sub (c.pow z e) (c.pow y e)
  let um := c.add u 2
  let up := c.add u 1
  let A := c.pow um a
  let C := c.pow up a
  let B := c.pow u a
  let T := c.red3 (c.mul z A + 2 * c.mul (c.add (z + 2 * y) 1) B + 2 * c.mul y C + c.mul A C)
  let P := c.mul (c.mul (c.mul u um) up) T
  some (s, a, c.pow P (q - 2))

end CFSG.KC.Misc.ReeGen

open CFSG.KC.Tab CFSG.KC.Misc.ReeGen in
elab "#ree_app " pre:ident kk:num pp:num nn:num : command => do
  let P := pre.getId
  let k := kk.getNat
  let F := enc pp.getNat nn.getNat
  let ML := (1 <<< (32 * k)) - 1
  let M15 := rep (2 * k + 2) 32767
  let c : Fld := ⟨k, 0, M15, ML⟩
  let G := c.red3 (2 * (F &&& ML))
  let c : Fld := { c with G := G }
  let q := 3 ^ k
  let nb := q.log2 + 1
  let isTrue := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
  let cst := fun (s : Name) => mkConst (P ++ s)
  let kE := lit k
  let ns := fun (e : Nat) => e.log2 + 1
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `F) natT (lit F)
    addDef (P ++ `G) natT (lit G)
    addDef (P ++ `M15) natT (lit M15)
    addDef (P ++ `ML) natT (lit ML)
    let setupT := isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.setupK)
      #[kE, cst `F, cst `G, cst `M15, cst `ML])
    addThm (P ++ `setup) setupT reflBoolTrue
    let rootT := isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.rootK)
      #[kE, cst `G, cst `M15, cst `ML, lit nb])
    addThm (P ++ `root) rootT reflBoolTrue
    let okT := fun (bE : Expr) => mkAppN (mkConst ``CFSG.KC.Misc.Ree.CaseOK)
      #[kE, cst `G, cst `M15, cst `ML, bE]
    let mut pfs : Array Expr := #[]
    for b in [0:k] do
      let nm := P ++ Name.mkSimple s!"c{b}"
      match caseData c b with
      | none =>
        let ty := isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.skipB) #[kE, lit b])
        addThm nm ty reflBoolTrue
        pfs := pfs.push (mkAppN (mkConst ``CFSG.KC.Misc.Ree.caseOK_skip)
          #[kE, cst `G, cst `M15, cst `ML, lit b, mkConst nm])
      | some (s, a, w) =>
        let args := #[kE, cst `G, cst `M15, cst `ML, lit b, lit s, lit a, lit w, lit (ns s),
          lit (ns a), lit (ns (3 ^ b + 1))]
        let ty := isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Ree.caseB) args)
        addThm nm ty reflBoolTrue
        pfs := pfs.push (mkAppN (mkConst ``CFSG.KC.Misc.Ree.caseOK_case) (args.push (mkConst nm)))
    let predE := mkLambda `b .default natT (okT (.bvar 0))
    let mut hb := mkApp (mkConst ``CFSG.KC.Misc.Ree.all_lt_zero) predE
    for b in [0:k] do
      hb := mkAppN (mkConst ``CFSG.KC.Misc.Ree.all_lt_succ) #[predE, lit b, hb, pfs[b]!]
    let pf := mkAppN (mkConst ``CFSG.KC.Misc.Ree.appOK_of)
      #[kE, cst `F, cst `G, cst `M15, cst `ML, lit nb, cst `setup, cst `root, hb]
    addThm (P ++ `ok) (mkApp (mkConst ``CFSG.Walter.Ree.Bombieri.AppOK) kE) pf

end
