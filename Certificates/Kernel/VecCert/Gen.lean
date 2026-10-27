module

public import CFSG.Certificates.Kernel.VecKSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.HS.Cert
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Sporadic.Th.F2Spec

open Lean Elab Command

public section

namespace CFSG.KC.VecGen

open CFSG.KC.Tab CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

meta def fld (X i d : Nat) : Nat := (X >>> (d * i)) % (1 <<< d)

meta def vm (d M v : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    if (v >>> k) % 2 == 1 then acc := acc ^^^ fld M k d
  return acc

meta def mulM (d A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:d] do
    r := r ||| (vm d B (fld A i d) <<< (d * i))
  return r

meta def idM (d : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:d] do
    r := r ||| ((1 <<< i) <<< (d * i))
  return r

meta def trM (d X : Nat) : Nat := Id.run do
  let mut r := 0
  for j in [0:d] do
    let mut row := 0
    for i in [0:d] do
      if (X >>> (d * i + j)) % 2 == 1 then row := row ||| (1 <<< i)
    r := r ||| (row <<< (d * j))
  return r

meta def powM (d M e : Nat) : Nat := Id.run do
  let mut r := idM d
  for _ in [0:e] do
    r := mulM d r M
  return r

meta def invM (d M : Nat) : Nat := Id.run do
  let one := idM d
  let mut cur := M
  for _ in [0:1000000] do
    let nx := mulM d cur M
    if nx == one then return cur
    cur := nx
  return 0

meta def packRows (d : Nat) (rows : Array Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:rows.size] do
    r := r ||| (rows[i]! <<< (d * i))
  return r

meta def letM (NA NAi NB NBi : Nat) (z : Int) : Nat :=
  if z = 1 then NA else if z = -1 then NAi else if z = 2 then NB else NBi

meta def wordM (d NA NAi NB NBi : Nat) (w : List Int) : Nat :=
  w.foldr (fun z acc => mulM d acc (letM NA NAi NB NBi z)) (idM d)

meta def slpM (d : Nat) (prog : List Instr) (R0 : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut R := R0
  let mut V : Array Nat := #[]
  for ins in prog do
    match ins with
    | .mu i j k => R := R.set! k (mulM d R[j]! R[i]!)
    | .pwr e i k => R := R.set! k (powM d R[i]! e)
    | .iv i k =>
      let x := invM d R[i]!
      V := V.push x
      R := R.set! k x
  return (R, V)

meta def orbitTwin (d NA NB v0 cap : Nat) : VOrbit := Id.run do
  let mut pos : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert v0 0
  let mut pts : Array Nat := #[v0]
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      let w := vm d NA v
      if !pos.contains w then
        pos := pos.insert w pts.size
        pts := pts.push w
      alpha := alpha.push (UInt32.ofNat pos[w]!)
      let u := vm d NB v
      if !pos.contains u then
        pos := pos.insert u pts.size
        pts := pts.push u
      beta := beta.push (UInt32.ofNat pos[u]!)
    else break
  return ⟨pts, alpha, beta⟩

meta def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def natList (xs : List Nat) : Expr := listE natT (xs.map lit)

meta def isTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name, levelParams := [], type, value }

meta def addNat (name : Name) (v : Nat) : CoreM Unit := addDef name natT (lit v)

meta def addTable (F : Name) (vals : Array Nat) : CoreM Unit := do
  let nl := (vals.size + 63) / 64
  let cnt := max nl 1
  let h := Nat.log2 (2 * cnt - 1)
  addDef (F ++ `Z) natT (lit 0)
  for k in [0:nl] do
    let mut acc := 0
    for t in [0:64] do
      let i := 64 * k + t
      if i < vals.size then acc := acc ||| (vals[i]! <<< (32 * t))
    addDef (F ++ Name.mkSimple s!"L{k}") natT (lit acc)
  let leaf := fun k => constFn (if k < nl then mkConst (F ++ Name.mkSimple s!"L{k}") else mkConst (F ++ `Z))
  addDef F fnT (table leaf (1 <<< h) 6)

meta def fnListT : Expr := mkApp (mkConst ``List [0]) fnT

meta def lt (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) a b

meta def forallLt (n f : Expr) : Expr :=
  mkForall `h .default natT (mkForall `hh .default (lt (mkBVar 0) (n.liftLooseBVars 0 1))
    (isTrue (mkApp (f.liftLooseBVars 0 2) (mkBVar 1))))

meta def coverOf (P : Name) (emit : String → Bool) (tag : String) (f nE : Expr) (n S : Nat) :
    CoreM Expr := do
  let ns := (n + S - 1) / S
  let sl := fun (s : Expr) => isTrue (mkApp3 (mkConst ``CFSG.KC.VecK.allS)
    (mkApp2 (mkConst ``Nat.mul) s (lit S)) (mkApp3 (mkConst ``CFSG.KC.VecK.sliceN) nE (lit S) s) f)
  let Pl := mkLambda `s .default natT (sl (mkBVar 0))
  let mut pf := mkApp (mkConst ``CFSG.KS.Raw.forall_lt_zero) Pl
  for s in [0:ns] do
    let nm := P ++ Name.mkSimple s!"{tag}_{s}"
    if emit tag && !(← getEnv).contains nm then
      addThm nm (sl (lit s)) reflBoolTrue
    pf := mkAppN (mkConst ``CFSG.KS.Raw.forall_lt_succ) #[Pl, lit s, pf, mkConst nm]
  let hle := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) nE (mkApp2 (mkConst ``Nat.mul) (lit ns) (lit S)) reflBoolTrue
  return mkAppN (mkConst ``CFSG.KC.VecK.allS_cover) #[lit S, lit ns, nE, f, pf, hle]

meta def chainOf (Q : Expr) (pfs : Array Expr) : Expr := Id.run do
  let mut pf := mkApp (mkConst ``CFSG.KS.Raw.forall_lt_zero) Q
  for s in [0:pfs.size] do
    pf := mkAppN (mkConst ``CFSG.KS.Raw.forall_lt_succ) #[Q, lit s, pf, pfs[s]!]
  return pf

end CFSG.KC.VecGen

open CFSG.KC.Tab CFSG.KC.VecGen CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native in
elab "#kvec " pre:ident dId:ident sN:num md:(str)? : command => do
  let P := pre.getId
  let S := sN.getNat
  let mode := (md.map (·.getString)).getD "all"
  let parts := mode.splitOn ","
  let doData := mode == "all" || parts.contains "data"
  let doOk := mode == "all" || parts.contains "ok"
  let emit : String → Bool := fun tag => mode == "all" || parts.any fun p =>
    tag == p || (p.endsWith "*" && tag.startsWith (String.ofList (p.toList.dropLast)))
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let Df ← liftTermElabM <| unsafe evalConst (Unit → VecData) dN
  let D := Df ()
  let DE := mkApp (mkConst dN) (mkConst ``Unit.unit)
  let pj := fun (f : Name) => mkApp (mkConst (``CFSG.Sporadic.SmallF2.Native.VecData ++ f)) DE
  let d := D.d
  let n := D.n
  let MA := packRows d D.rowsA
  let MB := packRows d D.rowsB
  let NA := trM d MA
  let NB := trM d MB
  let NAi := invM d NA
  let NBi := invM d NB
  let W0 := wordM d NA NAi NB NBi D.w0
  let W1 := wordM d NA NAi NB NBi D.w1
  let R0 := #[W0, W1] ++ Array.replicate (D.nregs - 2) (idM d)
  let (R, V) := slpM d D.prog R0
  let mut LM : Array Nat := #[]
  for j in [0:D.sel.size] do
    let x := R[D.sel[j]!]!
    LM := (LM.push x).push (invM d x)
  let BI := packRows d D.basisInv
  let O := orbitTwin d NA NB D.v0 n
  let R0t := regs0 D O
  let st := runSLP D.n D.prog R0t
  let L := lettersOf D.n D.sel st.1
  let T := chainTrees D.n L D.base
  let lv := levelLetters L D.base 1
  let Ss := D.subReps.map fun r => treeBFS D.n r L lv
  let labs := labelsOf D.n Ss
  let pts := O.pts
  let BM := packRows d (D.basis.map fun i => pts[i]!)
  let sorted := (Array.range n).qsort (fun a b => pts[a]! < pts[b]!)
  let Sv := sorted.map fun i => pts[i]!
  let mut IP := Array.replicate n 0
  for k in [0:n] do
    IP := IP.set! sorted[k]! k
  let kL := L.size
  let csA := D.seedA.toList
  let csB := D.seedB.toList
  let charE : Expr := mkConst ``Char
  let chE := fun (cs : List Char) => listE charE (cs.map fun ch => mkApp (mkConst ``Char.ofNat) (lit ch.toNat))
  let ofNat := fun (a : Array UInt32) => a.map (·.toNat)
  liftCoreM <| withOptions (Elab.async.set · false) do
   if doData then
    let lty := mkApp (mkConst ``List [0]) charE
    addDef (P ++ `csA) lty (chE csA)
    addDef (P ++ `csB) lty (chE csB)
    let strE := mkConst ``String
    let hAty := mkApp3 (mkConst ``Eq [1]) strE (pj `seedA) (mkApp (mkConst ``String.ofList) (mkConst (P ++ `csA)))
    let hBty := mkApp3 (mkConst ``Eq [1]) strE (pj `seedB) (mkApp (mkConst ``String.ofList) (mkConst (P ++ `csB)))
    addThm (P ++ `hA) hAty (mkApp2 (mkConst ``Eq.refl [1]) strE (pj `seedA))
    addThm (P ++ `hB) hBty (mkApp2 (mkConst ``Eq.refl [1]) strE (pj `seedB))
    for (nm, v) in [(`MA, MA), (`MB, MB), (`NA, NA), (`NB, NB), (`NAi, NAi), (`NBi, NBi), (`BI, BI),
        (`BM, BM), (`kL, kL)] do
      addNat (P ++ nm) v
    let lstT := mkApp (mkConst ``List [0]) natT
    addDef (P ++ `R) lstT (natList R.toList)
    addDef (P ++ `V) lstT (natList V.toList)
    addDef (P ++ `LM) lstT (natList LM.toList)
    addTable (P ++ `Pt) pts
    addTable (P ++ `AT) (ofNat O.alpha)
    addTable (P ++ `BT) (ofNat O.beta)
    addTable (P ++ `S) Sv
    addTable (P ++ `IP) IP
    addTable (P ++ `SP) sorted
    for j in [0:kL] do
      addTable (P ++ Name.mkSimple s!"LT{j}") (ofNat L[j]!)
    let fnLT := fun (nm : String) (k : Nat) => mkLambda `j .default natT
      (mkApp2 (mkConst ``CFSG.KC.VecK.getF) (listE fnT ((List.range k).map fun j =>
        mkConst (P ++ Name.mkSimple s!"{nm}{j}"))) (mkBVar 0))
    addDef (P ++ `LT) (mkForall `j .default natT fnT) (fnLT "LT" kL)
    for i in [0:T.size] do
      addTable (P ++ Name.mkSimple s!"Ot{i}") (ofNat T[i]!.pts)
      addTable (P ++ Name.mkSimple s!"IX{i}") (ofNat T[i]!.pos)
      addTable (P ++ Name.mkSimple s!"Op{i}") (ofNat T[i]!.par)
      addTable (P ++ Name.mkSimple s!"Ol{i}") (ofNat T[i]!.lab)
    for (nm : String) in ["Ot", "IX", "Op", "Ol"] do
      addDef (P ++ Name.mkSimple nm) (mkForall `j .default natT fnT) (fnLT nm T.size)
    for j in [0:Ss.size] do
      addTable (P ++ Name.mkSimple s!"St{j}") (ofNat Ss[j]!.pts)
      addTable (P ++ Name.mkSimple s!"Sp{j}") (ofNat Ss[j]!.par)
      addTable (P ++ Name.mkSimple s!"Sl{j}") (ofNat Ss[j]!.lab)
    for (nm : String) in ["St", "Sp", "Sl"] do
      addDef (P ++ Name.mkSimple s!"{nm}s") fnListT
        (listE fnT ((List.range Ss.size).map fun j => mkConst (P ++ Name.mkSimple s!"{nm}{j}")))
    addTable (P ++ `LB) labs
    let PSv := (Array.range n).map fun p => (Ss[labs[p]!]!.pos[p]!).toNat
    addTable (P ++ `PS) PSv
    let mut FO := Array.replicate n 0
    let mut seen := Array.replicate n false
    seen := seen.set! 0 true
    for k in [0:2 * n] do
      let x := if k % 2 == 0 then (O.alpha[k / 2]!).toNat else (O.beta[k / 2]!).toNat
      if x < n && !seen[x]! then
        seen := seen.set! x true
        FO := FO.set! x k
    addTable (P ++ `FO) FO
   do
    let c := fun (nm : Name) => mkConst (P ++ nm)
    let dE := pj `d
    let nE := pj `n
    let K := `CFSG.KC.VecK
    let baseF := mkApp2 (mkConst ``CFSG.KC.Co1F2.getL) (lit 0)
    let arrL := fun (e : Expr) => mkApp2 (mkConst ``Array.toList [0]) natT e
    let arrS := fun (e : Expr) => mkApp2 (mkConst ``Array.size [0]) natT e
    let getL := fun (L i : Expr) => mkApp3 (mkConst ``CFSG.KC.Co1F2.getL) (lit 0) L i
    let baseL := arrL (pj `base)
    let horb ← coverOf P emit "orb" (mkAppN (mkConst (K ++ `orbAt)) #[dE, nE, c `NA, c `NB, c `Pt, c `AT, c `BT])
      nE n S
    let hbfs ← coverOf P emit "bfs" (mkAppN (mkConst (K ++ `bfsAt)) #[nE, c `AT, c `BT, c `FO]) nE n S
    let hsort ← coverOf P emit "sort" (mkAppN (mkConst (K ++ `sortAt)) #[nE, c `Pt, c `S, c `IP, c `SP]) nE n S
    let fLet := fun (j : Expr) => mkAppN (mkConst (K ++ `letAt)) #[dE, nE, getL (c `LM) j, c `Pt,
      mkApp (c `LT) j]
    let mut pLet : Array Expr := #[]
    for j in [0:kL] do
      pLet := pLet.push (← coverOf P emit s!"let{j}" (fLet (lit j)) nE n S)
    let hLT := chainOf (mkLambda `j .default natT (forallLt nE (fLet (mkBVar 0)))) pLet
    let fTree := fun (i : Expr) => mkAppN (mkConst (K ++ `treeAt)) #[nE, c `kL, getL (pj `orbSizes) i, i,
      getL baseL i, c `LT, baseF baseL, mkApp (c `Ot) i,
      mkApp (c `IX) i, mkApp (c `Op) i, mkApp (c `Ol) i]
    let mut pTree : Array Expr := #[]
    for i in [0:T.size] do
      pTree := pTree.push (← coverOf P emit s!"tree{i}" (fTree (lit i)) (getL (pj `orbSizes) (lit i))
        T[i]!.pts.size S)
    let htree := chainOf (mkLambda `i .default natT (forallLt (getL (pj `orbSizes) (mkBVar 0))
      (fTree (mkBVar 0)))) pTree
    let getF := fun (L i : Expr) => mkApp2 (mkConst (K ++ `getF)) L i
    let fSub := fun (j : Expr) => mkAppN (mkConst (K ++ `subAt)) #[nE, c `kL, getL (pj `subSizes) j, j,
      getL (arrL (pj `subReps)) j, c `LT, baseF baseL,
      getF (c `Sts) j, c `LB, c `PS, getF (c `Sps) j, getF (c `Sls) j]
    let mut pSub : Array Expr := #[]
    for j in [0:Ss.size] do
      pSub := pSub.push (← coverOf P emit s!"sub{j}" (fSub (lit j)) (getL (pj `subSizes) (lit j))
        Ss[j]!.pts.size S)
    let hsub := chainOf (mkLambda `j .default natT (forallLt (getL (pj `subSizes) (mkBVar 0))
      (fSub (mkBVar 0)))) pSub
    let hlab ← coverOf P emit "lab" (mkAppN (mkConst (K ++ `labAt)) #[arrS (pj `subReps), pj `subSizes, c `Sts,
      c `LB, c `PS]) nE n S
    let r := reflBoolTrue
    let args : Array Expr := #[DE, lit 3, c `csA, c `csB, c `MA, c `MB, c `NA, c `NB, c `NAi, c `NBi,
      c `BI, c `BM, c `kL, c `Pt, c `AT, c `BT, c `FO, c `S, c `IP, c `SP, c `R, c `V, c `LM, c `LT,
      c `Ot, c `IX, c `Op, c `Ol, c `Sts, c `Sps, c `Sls, c `LB, c `PS,
      c `hA, c `hB, r, r, r, r, r, horb, hbfs, hsort, r, r, r, r, r, hLT, r, htree, r, hsub, hlab, r, r]
    if doOk then
      let app := mkAppN (mkConst (K ++ `vecK_sound)) args
      let ty ← Meta.MetaM.run' (Meta.inferType app)
      addThm (P ++ `ok) ty app
