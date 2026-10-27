module

public import Certificates.Kernel.SporSch.PairHS.Chain
public import Certificates.Data.Kernel.LocalQT.HSAutN
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Certificates.Data.Kernel.EvenSporDS81.FCDefs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import all Init.Data.List.SplitOn.Basic
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CFSG.KD.HS3850.S9T CFSG.EvenSporadicStandard.TwoHS.orbitStepsStr

namespace CFSG.KD.HS3850.S9

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CertificateChecks.KernelSporSch
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def letK (l : Fin 2 × Bool) : Nat :=
  if l.2 then PHSC.S l.1.val else PHSC.SI l.1.val

@[expose] noncomputable def HX (i : Nat) : Nat :=
  (hsGenWords.getD i []).foldl (fun a l => pc a (letK l)) idn

@[expose] noncomputable def B (j : Nat) : Nat :=
  (betaWords.getD j []).foldl (fun a l => pc a (HX (l - 1))) idn

@[expose] noncomputable def BSQ (j : Nat) : Nat := pc (B j) (B j)

@[expose] noncomputable def imgK (X p : Nat) : Nat := if p < 3850 then img X p else 0

@[expose] noncomputable def sigmaC : List Nat :=
  (List.range 3850).filter fun p => (List.range 3).all fun j => imgK (BSQ j) p == p

@[expose] noncomputable def stepsC : List (Nat × Nat) :=
  pairUp ((S9T.chars.splitOn ' ').map CFSG.KC.Str.decVal)

@[expose] def encL (w : Nat) (l : List Nat) : Nat := l.foldr (fun v acc => v + 2 ^ w * acc) 0

@[expose] noncomputable def parN : Nat := encL 13 (stepsC.map Prod.fst)

@[expose] noncomputable def genN : Nat := encL 3 (stepsC.map Prod.snd)

@[expose] def fdK (w x i : Nat) : Nat := x / 2 ^ (w * i) % 2 ^ w

@[expose] noncomputable def par (k : Nat) : Nat := fdK 13 parN (k - 1)

@[expose] noncomputable def gen (k : Nat) : Nat := fdK 3 genN (k - 1)

@[expose] noncomputable def ptK : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, k, x => if k = 0 then x else
      strictN (gen k) fun g => strictN (par k) fun p => imgK (HX g) (ptK f p x)

@[expose] noncomputable def setC (k : Nat) : List Nat := sigmaC.map (ptK k k)

@[expose] def dedupS : List Nat → List Nat
  | a :: b :: l => if a = b then dedupS (b :: l) else a :: dedupS (b :: l)
  | l => l

@[expose] def setKeyC (l : List Nat) : Nat :=
  (dedupS (CFSG.KC.EvenSporDS81.isortN l)).foldr (fun p acc => p + 4096 * acc) 0

theorem kLet : (List.range 2).all (fun i =>
    canonK 3850 12 (mask 12) (3850 * 12) (PHSC.S i) &&
    canonK 3850 12 (mask 12) (3850 * 12) (PHSC.SI i) &&
    invEqK 3850 12 (mask 12) (3850 * 12) (PHSC.S i) (PHSC.SI i)) = true := by
  decide +kernel

theorem kDigits : (S9T.chars.splitOn ' ').all (fun ds => !ds.isEmpty && ds.all Char.isDigit) =
    true := by
  decide +kernel

theorem kSteps : stepsC.length = 4124 ∧ (stepsC.zipIdx.all fun e =>
    e.1.1 == par (e.2 + 1) && e.1.2 == gen (e.2 + 1) && decide (e.1.1 ≤ e.2) &&
      decide (e.1.2 < 6)) = true := by
  decide +kernel

theorem kOrbit_neg : stepsC.length ≠ 4125 ∧
    (sigmaC.all fun p => imgK (B 0) p == p) = false := by
  decide +kernel

end CFSG.KD.HS3850.S9
