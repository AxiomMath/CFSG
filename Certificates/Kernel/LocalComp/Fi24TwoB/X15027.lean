module

public import Certificates.Kernel.LocalComp.Fi24TwoB.D15027
public import Certificates.Kernel.LocalComp.Fi24TwoB.Kd15027
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Sporadic.Fi24K.T2077
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Spor.ConjTree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

namespace CertificateChecks.KernelLC.Fi24BXM

open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

meta def keyOf (a : Array Nat) : Nat :=
  [4, 0, 1, 2, 3, 6].foldr (fun p acc => a[p]! + 504 * acc) 0

meta def mem (o : Nat) : Array (Array Nat) :=
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NOrbConjs[o]!

meta def m0 : Array (Array Nat) := mem 0
meta def m1 : Array (Array Nat) := mem 1
meta def m2 : Array (Array Nat) := mem 2

meta def order (o : Nat) : List Nat :=
  let a := mem o
  ((Array.range a.size).qsort fun x y => keyOf a[x]! < keyOf a[y]!).toList

meta def k0 : List Nat := order 0
meta def k1 : List Nat := order 1
meta def k2 : List Nat := order 2

meta def reps : Array (Array Nat) := #[fi24NOrbReps[0]!, fi24NOrbReps[2]!]

end CertificateChecks.KernelLC.Fi24BXM

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.Fi24BX.X0 CertificateChecks.KernelLC.Fi24BXM.m0 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BX.X1 CertificateChecks.KernelLC.Fi24BXM.m1 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BX.X2 CertificateChecks.KernelLC.Fi24BXM.m2 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BX.R CertificateChecks.KernelLC.Fi24BXM.reps 9
#kss_natlist CertificateChecks.KernelLC.Fi24BX.KT0 CertificateChecks.KernelLC.Fi24BXM.k0
#kss_natlist CertificateChecks.KernelLC.Fi24BX.KT1 CertificateChecks.KernelLC.Fi24BXM.k1
#kss_natlist CertificateChecks.KernelLC.Fi24BX.KT2 CertificateChecks.KernelLC.Fi24BXM.k2

namespace CertificateChecks.KernelLC.Fi24BX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.ConjTree
open CertificateChecks.KernelLC CertificateChecks.KernelSpor

@[expose] noncomputable def X (o : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) X0
    (fun o' _ => Nat.rec (motive := fun _ => Nat → Nat) X1 (fun _ _ => X2) o') o

@[expose] noncomputable def TF (o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Fi24BT.T0.F
    (fun o' _ => Nat.rec (motive := fun _ => Nat) Fi24BT.T1.F (fun _ _ => Fi24BT.T2.F) o') o

@[expose] def NT (o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1700 (fun o' _ => Nat.rec (motive := fun _ => Nat) 377
    (fun _ _ => 2015) o') o

@[expose] noncomputable def SK (o : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) ((List.range 1701).map KT0)
    (fun o' _ => Nat.rec (motive := fun _ => List Nat) ((List.range 378).map KT1)
      (fun _ _ => (List.range 2016).map KT2) o') o

@[expose] noncomputable def st (o s : Nat) : Bool :=
  stepSl 504 9 5 Fi24BKd.S Fi24BKd.SI (X o) (TF o) 16 (NT o) (Nat.mul s 20) 20

@[expose] noncomputable def st0 (s : Nat) : Bool := st 0 s
@[expose] noncomputable def st1 (s : Nat) : Bool := st 1 s
@[expose] noncomputable def st2 (s : Nat) : Bool := st 2 s

theorem keys0 : keysSK 504 9 [4, 0, 1, 2, 3, 6] 1701 (X 0) (SK 0) = true := by quickRfl
theorem keys1 : keysSK 504 9 [4, 0, 1, 2, 3, 6] 378 (X 1) (SK 1) = true := by quickRfl
theorem keys2 : keysSK 504 9 [4, 0, 1, 2, 3, 6] 2016 (X 2) (SK 2) = true := by quickRfl

theorem kFirst : (Nat.beq (X 0 0) (R 0) && Nat.beq (X 1 0) (Fi24ST.T 0) &&
    Nat.beq (X 2 0) (R 1)) = true := by quickRfl

theorem kRep : (allN 2 (fun i => bAnd(canonK 504 9 (mask 9) (504 * 9) (R i),
    permOK 504 9 (mask 9) (504 * 9) (R i) (pinvS 504 9 (mask 9) (R i))))) = true := by quickRfl

theorem kRows : allN 2 (fun j => Nat.beq (R j) (pg 4536 (mask 4536) Fi24BT.Rep.F j)) = true := by
  quickRfl

end CertificateChecks.KernelLC.Fi24BX

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.Fi24BX.st0 0 85
#kon_join CertificateChecks.KernelLC.Fi24BX.st0All CertificateChecks.KernelLC.Fi24BX.st0 85
#kon_slices CertificateChecks.KernelLC.Fi24BX.st1 0 19
#kon_join CertificateChecks.KernelLC.Fi24BX.st1All CertificateChecks.KernelLC.Fi24BX.st1 19
#kon_slices CertificateChecks.KernelLC.Fi24BX.st2 0 101
#kon_join CertificateChecks.KernelLC.Fi24BX.st2All CertificateChecks.KernelLC.Fi24BX.st2 101

end
