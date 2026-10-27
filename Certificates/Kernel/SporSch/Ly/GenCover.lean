module

public meta import Lean
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Sporadic.Schreier.LyCheckCover
public import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.SporSch.Ly.GenLy

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_cover " pre:ident : command => do
  let P := pre.getId
  let b4 := powM 5 111 (matB ()) 4
  let cs := cStarArr b4
  let T := transTab cs
  let tt := (Array.range 121).map fun q => packM (tabAt T (q / 11) (q % 11)).1
  let tti := (Array.range 121).map fun q => packM (tabAt T (q / 11) (q % 11)).2
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `TT) tt
    addTree (P ++ `TTI) tti

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kly_rels " pre:ident qId:ident : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  liftCoreM <| withOptions (Elab.async.set · false) do
    addChain2 P "rel" "hrel" 121 12 fun q => isTrue (mkApp (mkConst qN) q)

end
