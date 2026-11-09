module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Sporadic.Schreier.SteinbergBSLyOuterCheck
public import Certificates.Data.Kernel.SporSch.LyMat
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Sporadic.Schreier.LyCheckCover
public meta import CFSG.Sporadic.Schreier.LyCheckSeven
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.LyGen

open CFSG.KC.Tab CFSG.KS.RawGen
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

meta def packM (M : Array (Array Nat)) : Nat := Id.run do
  let mut acc := 0
  for i in [0:111] do
    for j in [0:111] do
      acc := acc ||| (((M[i]!)[j]! % 5) <<< (1332 * i + 12 * j))
  return acc

meta def unpackM (X : Nat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    (X >>> (1332 * i.val + 12 * j.val)) % 4096

meta partial def lyBytesLE (n L : Nat) : ByteArray :=
  if L ≤ 8 then Id.run do
    let mut b := ByteArray.empty
    for k in [0:L] do
      b := b.push (n >>> (8 * k)).toUInt8
    return b
  else
    let h := L / 2
    lyBytesLE (n % (1 <<< (8 * h))) h ++ lyBytesLE (n >>> (8 * h)) (L - h)

meta def lyEncode (secs : Array (Array Nat)) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for s in secs do
    b := b ++ lyBytesLE s.size 4
    for n in s do
      let L := if n = 0 then 0 else n.log2 / 8 + 1
      b := b ++ lyBytesLE L 4 ++ lyBytesLE n L
  return b

meta def lyDecode (b : ByteArray) : Array (Array Nat) := Id.run do
  let mut i := 0
  let mut secs : Array (Array Nat) := #[]
  while i + 4 ≤ b.size do
    let c := natLE b i (i + 4)
    i := i + 4
    let mut s : Array Nat := #[]
    for _ in [0:c] do
      let L := natLE b i (i + 4)
      s := s.push (natLE b (i + 4) (i + 4 + L))
      i := i + 4 + L
    secs := secs.push s
  return secs

meta def lyRoot : CommandElabM System.FilePath := do
  let m ← getMainModule
  if m.isAnonymous || m == `_stdin then return "."
  let mut p := System.FilePath.mk (← getFileName)
  for _ in m.components do
    p := p.parent.getD "."
  return if p.toString.isEmpty then "." else p

meta def lyRead (rel : String) (size hash : Nat) : CommandElabM (Array (Array Nat)) := do
  let path := (← lyRoot) / rel
  let b ← IO.FS.readBinFile path
  unless b.size == size && b.hash.toNat == hash do
    throwError "data file {path}: size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  return lyDecode b

meta def intListE (l : List Int) : Expr :=
  let intT := mkConst ``Int
  l.foldr (fun z acc => mkApp3 (mkConst ``List.cons [0]) intT
    (if z ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit z.toNat)
      else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((-z).toNat - 1))) acc)
    (mkApp (mkConst ``List.nil [0]) intT)

meta def chainPrefix (g gi : Nat → Mat) (word : List Int) (c : Nat) : Mat × Array Nat := Id.run do
  let m := (word.length + c - 1) / c
  let mut X := idM 111
  let mut ks : Array Nat := #[packM X]
  for k in [0:m] do
    X := wordFromM g gi X ((word.drop (k * c)).take c)
    ks := ks.push (packM X)
  return (X, ks)

meta def bsSections (_ : Unit) : Array (Array Nat) :=
  let A := matA ()
  let B := matB ()
  let b4 := powM 5 111 B 4
  let g := fun (k : Nat) => if k = 0 then A else B
  let gi := fun (k : Nat) => if k = 0 then A else b4
  let (c0, k0s) := chainPrefix g gi seedWord0 16
  let (c1, k1s) := chainPrefix g gi seedWord1 16
  let cs := extendM #[(c0, invM 5 111 c0), (c1, invM 5 111 c1)] cDerivations.toList
  let us := sylowGens cs
  let ts := (Array.range 10).map fun i => bsTM cs i
  let mf := mulM 5 111 (mulM 5 111 (mulM 5 111 us[2]! us[1]!) us[2]!) us[1]!
  let hm := r3eHM b4
  let mg := r3eGM hm mf
  #[#[packM A, packM B, packM b4], k0s, k1s, cs.map (packM ·.1), cs.map (packM ·.2),
    #[packM us[1]!, packM us[2]!], ts.map packM, #[packM mf, packM hm, packM mg]]

meta def sylowSections (cs : Array (Mat × Mat)) (Hh : Nat) : Array (Array Nat) :=
  let us := sylowGens cs
  let (pts, par, _, lam) := sylowBFS us 256
  let c := pts.size
  let ws := (Array.range c).map fun h =>
    (List.range us.size).foldl (fun acc k => acc ||| ((lam[k]!)[h]! <<< (9 * k))) 0
  let keys := pts.map packM
  let so := (Array.range c).qsort fun a b => keys[a]! < keys[b]!
  let soi := Id.run do
    let mut r := Array.replicate c 0
    for i in [0:c] do
      r := r.set! so[i]! i
    return r
  let nS := 256 / Hh
  let C := (Array.range (nS + 1)).map fun q =>
    min c (1 + ((List.range c).filter fun j => 0 < j && par[j]! < q * Hh).length)
  #[us.map packM, keys, ws, so, soi, C, #[Hh]]

meta def bsFile : String × Nat × Nat := ("Certificates/Kernel/SporSch/Ly/data/LyBS.bin", 4658132,
  10819306408737766214)

meta def sylowFile : String × Nat × Nat := ("Certificates/Kernel/SporSch/Ly/data/LySy.bin", 4848529,
  7949675446553695037)

meta def forallLtE (m : Nat) (body : Expr → Expr) : Expr :=
  mkForall `k .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit m]) (body (mkBVar 1)))

end CFSG.KS.SporSch.LyGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_bsdata " pre:ident : command => do
  let P := pre.getId
  let s ← lyRead bsFile.1 bsFile.2.1 bsFile.2.2
  unless s.size == 8 do throwError "{bsFile.1}: {s.size} sections, expected 8"
  let intLT := mkApp (mkConst ``List [0]) (mkConst ``Int)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `A) natT (lit s[0]![0]!)
    addDef (P ++ `B) natT (lit s[0]![1]!)
    addDef (P ++ `B4) natT (lit s[0]![2]!)
    addTree (P ++ `CF) s[3]!
    addTree (P ++ `CI) s[4]!
    addDef (P ++ `ncs) natT (lit s[3]!.size)
    addDef (P ++ `U1) natT (lit s[5]![0]!)
    addDef (P ++ `U2) natT (lit s[5]![1]!)
    addTree (P ++ `TS) s[6]!
    addDef (P ++ `MF) natT (lit s[7]![0]!)
    addDef (P ++ `HM) natT (lit s[7]![1]!)
    addDef (P ++ `MG) natT (lit s[7]![2]!)
    addDef (P ++ `W0) intLT (intListE seedWord0)
    addDef (P ++ `W1) intLT (intListE seedWord1)
    addTree (P ++ `K0) s[1]!
    addTree (P ++ `K1) s[2]!

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_sylowdata " pre:ident hh:num : command => do
  let P := pre.getId
  let Hh := hh.getNat
  let s ← lyRead sylowFile.1 sylowFile.2.1 sylowFile.2.2
  unless s.size == 7 && s[6]! == #[Hh] do
    throwError "{sylowFile.1}: {s.size} sections, expected 7 with last section #[{Hh}]"
  let us := s[0]!
  let c := s[1]!.size
  let nS := 256 / Hh
  let cst := fun (nm : Name) => mkConst nm
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `UG) us
    addTree (P ++ `E) s[1]!
    addTree (P ++ `W) s[2]!
    addTree (P ++ `ST) s[3]!
    addTree (P ++ `SIT) s[4]!
    addTree (P ++ `C) s[5]!
    addDef (P ++ `c) natT (lit c)
    addDef (P ++ `nS) natT (lit nS)
    let L := cst `CFSG.KD.OrdLy.L
    let H := cst `CFSG.KD.OrdLy.H
    let CM := cst `CFSG.KD.OrdLy.CM
    let RM := cst `CFSG.KD.OrdLy.RM
    let ty := fun (q : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
      (mkAppN (mkConst ``CFSG.KS.SporSch.LyM.runB) #[lit 5, lit 12, lit 1332, lit 111, lit 8, L, H,
        CM, RM, cst (P ++ `UG), cst (P ++ `E), cst (P ++ `W), lit us.size, lit c, lit Hh,
        mkApp2 (mkConst ``Nat.mul) q (lit Hh), mkApp (cst (P ++ `C)) q])
      (mkApp (cst (P ++ `C)) (mkApp (mkConst ``Nat.succ) q)))
    for q in [0:nS] do
      let nm := P ++ Name.mkSimple s!"run{q}"
      let tyq := ty (lit q)
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyq, value := reflBoolTrue }
    let lam' := mkLambda `q .default natT (ty (mkBVar 0))
    let v := forallChain lam' nS fun q => mkConst (P ++ Name.mkSimple s!"run{q}")
    let nmAll := P ++ `hrun
    let tyAll := forallLtE nS ty
    CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyAll, value := v }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_bschain " pre:ident wId:ident gId:ident giId:ident kId:ident cc:num : command => do
  let P := pre.getId
  let c := cc.getNat
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let giN ← liftCoreM <| realizeGlobalConstNoOverload giId
  let K := P ++ kId.getId
  let word : List Int := if wId.getId.toString.endsWith "W0" then seedWord0 else seedWord1
  let A := matA ()
  let B := matB ()
  let b4 := powM 5 111 B 4
  let g := fun (k : Nat) => if k = 0 then A else B
  let gi := fun (k : Nat) => if k = 0 then A else b4
  let m := (word.length + c - 1) / c
  let known := (← getEnv).contains K
  let ks := if known then #[] else (chainPrefix g gi word c).2
  let cst := fun (nm : Name) => mkConst nm
  let natE := natT
  let _ := natE
  liftCoreM <| withOptions (Elab.async.set · false) do
    unless known do addTree K ks
    addDef (K ++ `m) natT (lit m)
    let L := cst `CFSG.KD.OrdLy.L
    let H := cst `CFSG.KD.OrdLy.H
    let CM := cst `CFSG.KD.OrdLy.CM
    let RM := cst `CFSG.KD.OrdLy.RM
    let ty := fun (k : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
      (mkAppN (mkConst ``CFSG.KS.SporSch.LyM.wordR) #[lit 5, lit 12, lit 1332, lit 111, lit 8, L, H,
        CM, RM, cst gN, cst giN, mkApp (cst K) k,
        mkApp3 (mkConst ``List.take [0]) (mkConst ``Int) (lit c)
          (mkApp3 (mkConst ``List.drop [0]) (mkConst ``Int) (mkApp2 (mkConst ``Nat.mul) k (lit c))
            (cst wN))])
      (mkApp (cst K) (mkApp (mkConst ``Nat.succ) k)))
    for k in [0:m] do
      let nm := K ++ Name.mkSimple s!"c{k}"
      let tyk := ty (lit k)
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyk, value := reflBoolTrue }
    let lam := mkLambda `k .default natT (ty (mkBVar 0))
    let v := forallChain lam m fun k => mkConst (K ++ Name.mkSimple s!"c{k}")
    let nmAll := K ++ `all
    let tyAll := forallLtE m ty
    CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyAll, value := v }

end
