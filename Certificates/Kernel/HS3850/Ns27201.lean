module

public import Certificates.Kernel.HS3850.Fus
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixNsData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def nsG (r : Fin 4) (i : Nat) : Nat := HC.F (Nat.add (hnsBase r) i)

@[expose] noncomputable def nsGI (r : Fin 4) (i : Nat) : Nat := pinvS 3850 12 (mask 12) (nsG r i)

@[expose] noncomputable def nsEV (r : Fin 4) (wd : List (Fin 4 × Bool)) : Nat :=
  wd.foldl (fun acc l => pc acc (cond l.2 (nsG r l.1.val) (nsGI r l.1.val))) idn

@[expose] noncomputable def ck27201 (r : Fin 4) : Bool :=
  bAnd(allN 4 (fun i => strictB (nsGI r i) (fun R =>
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) R, invEqK 3850 12 (mask 12) (3850 * 12) (nsG r i) R))),
  strictB (nsEV r (hnsWordA r)) (fun A => strictB (nsEV r (hnsWordB r)) (fun B =>
    bAnd(ordK A 2, bAnd(ordK B 3, ordK (pc A B) 5)))))

theorem ok27201_0 : ck27201 0 = true := by quickRfl

theorem ok27201_1 : ck27201 1 = true := by quickRfl

theorem ok27201_2 : ck27201 2 = true := by quickRfl

theorem ok27201_3 : ck27201 3 = true := by quickRfl

end CFSG.KD.HS3850

end
