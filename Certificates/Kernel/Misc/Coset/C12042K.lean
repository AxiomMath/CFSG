module

public import Certificates.Data.Kernel.Misc.Coset.Mat
public import CFSG.LieType.Multipliers.G23Data
public import CFSG.Certificates.Kernel.Bounds.XG23R.Route
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelMiscCoset.C12042

open CFSG.KC.MiscCoset.Mat CFSG.LieType.Multipliers CFSG.LieType.Multipliers.G23

set_option maxRecDepth 100000

@[expose] noncomputable def rootL : ℕ → List (List ℕ)
  | 0 => rowsOf (rootMat 0)
  | 1 => rowsOf (rootMat 1)
  | 2 => rowsOf (rootMat 2)
  | _ => rowsOf (rootMat 3)

@[expose] noncomputable def aL : List (List ℕ) := wordL 3 14 rootL (aWord.map Fin.val)

@[expose] noncomputable def bL : List (List ℕ) := wordL 3 14 rootL (bWord.map Fin.val)

@[expose] noncomputable def biL : List (List ℕ) := mulL 3 14 bL bL

@[expose] noncomputable def letL : ℕ → List (List ℕ)
  | 0 => aL
  | 1 => aL
  | 2 => bL
  | _ => biL

@[expose] def codeN (l : ℕ × Bool) : ℕ := 2 * l.1 + if l.2 then 0 else 1

@[expose] def codeL (l : Fin 2 × Bool) : ℕ := codeN (l.1.val, l.2)

theorem k_aa : eqM (mulL 3 14 aL aL) (idL 14) = true := by quickRfl

theorem k_bb : eqM (mulL 3 14 bL biL) (idL 14) = true := by quickRfl

theorem k_rels : (CFSG.KBRoute.XG23R.rels.all fun r =>
    eqM (wordL 3 14 letL (r.map codeN)) (idL 14)) = true := by
  quickRfl

theorem k_gen : ((List.finRange 4).all fun j =>
    eqM (wordL 3 14 letL ((genWord j).map codeL)) (rootL j.val)) = true := by
  quickRfl

theorem k_comm : ((List.finRange 2).all fun i =>
    eqM (wordL 3 14 letL ((commWords (pairs i)).map codeL)) (letL (codeL (i, true)))) = true := by
  quickRfl

end CertificateChecks.KernelMiscCoset.C12042

end
