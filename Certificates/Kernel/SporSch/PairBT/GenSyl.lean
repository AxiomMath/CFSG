module

public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.GenBT

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.MBTG in
elab "#kss_reps " pre:ident nn:num ww:num hId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let reps ← match parseHint n (← evalStr hId) with
    | .ok r => pure r
    | .error e => throwError e
  withSync do
    addDef (P ++ `XL) listT (listE (reps.map fun p => pack w p.1).toList)
