module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Certificates.Kernel.Spor.RawSlPAppend
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_lvq " pre:ident ii:num lo:num hi:num ll:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let L := ll.getNat
  unless L > 0 && LCH % L == 0 do throwError "the piece length {L} does not divide {LCH}"
  let q := LCH / L
  let i := ii.getNat
  let iE := lit i
  let hsz := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let pre := #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS,
    c.steps iE, mkApp (c.k `LR) iE]
  let pT := fun (loE lenE : Expr) =>
    isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlKP) (pre ++ #[loE, lenE]))
  withSync do
    for s in [lo.getNat:hi.getNat] do
      let base := s * LCH
      let qN := fun (j : Nat) => P ++ Name.mkSimple s!"lsQ{i}_{s}_{j}"
      for j in [0:q] do
        addRefl (qN j) (pT (lit (base + j * L)) (lit L))
      let mut acc := mkConst (qN 0)
      for j in [1:q] do
        acc := mkAppN (mkConst ``CFSG.KS.Raw.lvSlKP_append)
          (pre ++ #[lit base, lit (j * L), lit L, acc, mkConst (qN j)])
      let sE := lit s
      let pN := P ++ Name.mkSimple s!"lsP{i}_{s}"
      CFSG.KC.addThmDecl <|
        { name := pN, levelParams := [], type := pT (mulE sE (lit LCH)) (lit LCH), value := acc }
      let v := mkAppN (mkConst ``CFSG.KS.Raw.lvSlK_of_P)
        #[c.nE, c.wE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS, c.steps iE,
          mkApp (c.k `LR) iE, mulE sE (lit LCH), lit LCH, hsz, mkConst pN]
      let nm := P ++ Name.mkSimple s!"ls{i}_{s}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := lvSlT c LCH iE sE, value := v }

end
