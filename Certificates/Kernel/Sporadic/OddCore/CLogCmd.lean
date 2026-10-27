module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.CosetLogSlices
public import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Sporadic.OddCore.CLogGenZ
public meta import Lean
public import CFSG.Certificates.Kernel.CosetLogSound

open Lean Elab Command

public section

meta def kclogMask (subs : List Nat) : Nat := subs.foldl (fun a c => a ||| (1 <<< c)) 0

elab "#kclog " P:ident mm:num nn:num rels:term:max subs:term:max zs:term:max cc:num kk:num :
    command => do
  let some subL := (match subs with
    | `([$xs,*]) => xs.getElems.toList.mapM (fun x => x.raw.isNatLit?)
    | _ => none) | throwErrorAt subs "expected a list of numerals"
  let some zL := (match zs with
    | `([$xs,*]) => xs.getElems.toList.mapM (fun x => x.raw.isNatLit?)
    | _ => none) | throwErrorAt zs "expected a list of numerals"
  let p := P.getId
  let n (s : String) : Ident := mkIdent (p ++ Name.mkSimple s)
  let lit (k : Nat) : TSyntax `num := Syntax.mkNumLit (toString k)
  let m := mm.getNat
  let K := kk.getNat
  let sm := lit (kclogMask subL)
  let L := lit (2 * m)
  let cmds : Array (TSyntax `command) := #[
    ← `(meta def $(n "relsM") : Array (Array Nat) :=
          (($rels : List (List Nat)).map List.toArray).toArray),
    ← `(meta def $(n "logM") : CertificateChecks.KernelSpor.CLogGen.Log × Array Nat :=
          CertificateChecks.KernelSpor.CLogGen.runZ $L $(n "relsM") $subs $zs $cc),
    ← `(meta def $(n "fdM") : Array Nat := $(n "logM").1.fd),
    ← `(meta def $(n "fwM") : Array Nat := $(n "logM").1.fw),
    ← `(meta def $(n "fsM") : Array Nat := $(n "logM").1.fs),
    ← `(meta def $(n "sdM") : Array Nat := $(n "logM").1.sd),
    ← `(meta def $(n "dtM") : Array Nat := $(n "logM").1.dt),
    ← `(meta def $(n "rnM") : Array Nat := $(n "relsM").map (·.size)),
    ← `(meta def $(n "nM") : Array Nat :=
          #[$(n "logM").1.fd.size, $(n "logM").1.nc] ++ $(n "logM").2),
    ← `(#krowsw $(n "FD") 34 $(n "fdM")),
    ← `(#krows $(n "FW") $(n "fwM")),
    ← `(#krows $(n "FS") $(n "fsM")),
    ← `(#krows $(n "SD") $(n "sdM")),
    ← `(#krows $(n "DT") $(n "dtM")),
    ← `(#krows $(n "RN") $(n "rnM")),
    ← `(#krows $(n "N") $(n "nM")),
    ← `(#kmisc_packarrs $(n "RL") $(n "relsM") 4),
    ← `(@[expose] noncomputable def $(n "sl") (s : Nat) : Bool :=
          CFSG.KC.CLog.factSlK $mm $nn (CFSG.KS.PEnum.r32 $(n "N") 1) $sm
            (CFSG.KS.PEnum.r32 $(n "N") 0) $(n "RL") (CFSG.KS.PEnum.r32 $(n "RN")) $(n "FD")
            $(n "FS") $(n "FW") $(n "SD") $(n "DT") (Nat.mul (nat_lit 4000) s) (nat_lit 4000)),
    ← `(theorem $(n "defs") : CFSG.KC.Enum.allN (CFSG.KS.PEnum.r32 $(n "N") 1)
          (CFSG.KC.CLog.defK (CFSG.KS.PEnum.r32 $(n "N") 0) $(n "FD") $(n "DT")) = true := by
          quickRfl),
    ← `(theorem $(n "nf") : Nat.ble (CFSG.KS.PEnum.r32 $(n "N") 0) $(lit (4000 * K)) = true := by
          quickRfl)]
  let hds ← (zL.zipIdx.toArray).mapM fun (z, j) =>
    `(theorem $(n s!"hd_{j}") : CFSG.KC.CLog.hdK $mm $nn (CFSG.KS.PEnum.r32 $(n "N") 0)
        (CFSG.KS.PEnum.r32 $(n "N") $(lit (2 + j))) $sm $(lit z) $rels $subs $(n "RL")
        (CFSG.KS.PEnum.r32 $(n "RN")) $(n "FD") = true := by
        quickRfl)
  let sls ← (Array.range K).mapM fun s =>
    `(theorem $(n s!"sl_{s}") : $(n "sl") $(lit s) = true := by quickRfl)
  let slIds : Array Term := (Array.range K).map fun s => n s!"sl_{s}"
  let all ← `(theorem $(n "slices") : ∀ s < $kk, $(n "sl") s = true := by
      intro s hs
      interval_cases s
      exacts [$slIds,*])
  for c in cmds ++ hds ++ sls ++ #[all] do
    elabCommand c

end
