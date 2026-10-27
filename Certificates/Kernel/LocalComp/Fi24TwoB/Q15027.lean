module

public import Certificates.Kernel.LocalComp.Fi24TwoB.E15027
public import Certificates.Kernel.LocalComp.Fi24TwoB.X15027
public import Certificates.Kernel.LocalComp.Fi24TwoB.A15027
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
meta import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

namespace CertificateChecks.KernelLC.Fi24BQM

open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CFSG.Sporadic.FischerOddCore

meta def keyOf (a : Array Nat) : Nat :=
  [4, 0, 1, 2, 3, 6].foldr (fun p acc => a[p]! + 504 * acc) 0

meta def pts : Array (Array Nat) := (CFSG.KC.BfsGen.search 504 9 fi24NGens).1

meta def ptIdx : Std.HashMap Nat Nat :=
  (List.range pts.size).foldl (fun m i => m.insert (keyOf pts[i]!) i) {}

meta def memIdx : Std.HashMap Nat (Nat × Nat) := Id.run do
  let mut m : Std.HashMap Nat (Nat × Nat) := {}
  for o in [0:3] do
    let a := fi24NOrbConjs[o]!
    for j in [0:a.size] do
      m := m.insert (keyOf a[j]!) (o, j)
  return m

meta def covO : List Nat := pts.toList.map fun a =>
  if a == Array.range 504 then 3 else ((memIdx.get? (keyOf a)).getD (4, 0)).1

meta def covJ : List Nat := pts.toList.map fun a =>
  if a == Array.range 504 then 0 else ((memIdx.get? (keyOf a)).getD (4, 0)).2

meta def w378 : List Nat := (List.range 378).map fun j => (ptIdx.get? (keyOf fi24T[j]!)).getD 0

meta def inL1 (a : Array Nat) : Nat := ((memIdx.get? (keyOf a)).getD (4, 0)).2

meta def wGen : List Nat := (List.range 12).map fun k => inL1 fi24NGens[k]!

meta def wProd : List Nat := [inL1 fi24T[340]!, inL1 fi24T[80]!]

meta def wQ : List Nat := fi24QWords.map fun e =>
  (ptIdx.get? (keyOf (CFSG.ComponentClassification.RankTwoSporadic.Cert.powA 504
    (fi24KWordA e.1) e.2))).getD 0

end CertificateChecks.KernelLC.Fi24BQM

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelLC.Fi24BQ.CO CertificateChecks.KernelLC.Fi24BQM.covO
#kss_natlist CertificateChecks.KernelLC.Fi24BQ.CJ CertificateChecks.KernelLC.Fi24BQM.covJ
#kss_natlist CertificateChecks.KernelLC.Fi24BQ.W CertificateChecks.KernelLC.Fi24BQM.w378
#kss_natlist CertificateChecks.KernelLC.Fi24BQ.WG CertificateChecks.KernelLC.Fi24BQM.wGen
#kss_natlist CertificateChecks.KernelLC.Fi24BQ.WP CertificateChecks.KernelLC.Fi24BQM.wProd
#kss_natlist CertificateChecks.KernelLC.Fi24BQ.WQ CertificateChecks.KernelLC.Fi24BQM.wQ

namespace CertificateChecks.KernelLC.Fi24BQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CertificateChecks.KernelLC CertificateChecks.KernelSpor CertificateChecks.KernelLC.Fi24B

@[expose] def NM (o : Nat) : Nat := Nat.succ (Fi24BX.NT o)

@[expose] noncomputable def covK (i : Nat) : Bool :=
  strictB (CO i) fun o => bIf(Nat.beq o 3, Nat.beq (Fi24BN.T i) (pidn 504 9),
    bAnd(Nat.blt o 3, bAnd(Nat.blt (CJ i) (NM o), Nat.beq (Fi24BX.X o (CJ i)) (Fi24BN.T i))))

@[expose] noncomputable def cov (s : Nat) : Bool := allN 1024 fun d => covK (Nat.add (s * 1024) d)

@[expose] noncomputable def sq (s : Nat) : Bool := allN 32 fun d =>
  strictB (Fi24BN.T (Nat.add (s * 32) d)) fun t => Nat.beq (pcomp 504 9 (mask 9) t t) (pidn 504 9)

@[expose] noncomputable def powK (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 504 9) (fun _ acc => pcomp 504 9 (mask 9) p acc) e

@[expose] noncomputable def wq (k : Nat) : Bool :=
  bAnd(Nat.blt (WQ k) 4096, Nat.beq (Fi24BN.T (WQ k))
    (powK (wordK (fi24QWords[k]!).1) (fi24QWords[k]!).2))

@[expose] noncomputable def sg (k : Nat) : Bool :=
  siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR Fi24BKd.TRI Fi24BKd.BP 7 0 (Fi24BN.G k)

theorem kW : allN 378 (fun j => bAnd(Nat.blt (W j) 4096, Nat.beq (Fi24BN.T (W j)) (Fi24ST.T j))) =
    true := by quickRfl

theorem kGens : allN 12 (fun k => bAnd(Nat.beq (Fi24BN.G k) (Fi24ST.T (fi24NBasis[k]!)),
    permOK 504 9 (mask 9) (504 * 9) (Fi24BN.G k) (pinvS 504 9 (mask 9) (Fi24BN.G k)))) = true := by
  quickRfl

theorem kWG : allN 12 (fun k => bAnd(Nat.blt (WG k) 378, Nat.beq (Fi24BX.X 1 (WG k)) (Fi24BN.G k))) =
    true := by quickRfl

theorem kProd : (Nat.beq (pcomp 504 9 (mask 9) (Fi24BX.X 0 0) (Fi24BX.X 0 58)) (Fi24ST.T 340) &&
    Nat.blt (WP 0) 378 && Nat.beq (Fi24BX.X 1 (WP 0)) (Fi24ST.T 340) &&
    Nat.beq (pcomp 504 9 (mask 9) (Fi24BX.X 2 0) (Fi24BX.X 2 3)) (Fi24ST.T 80) &&
    Nat.blt (WP 1) 378 && Nat.beq (Fi24BX.X 1 (WP 1)) (Fi24ST.T 80)) = true := by quickRfl

theorem kSift0 : allN 6 sg = true := by quickRfl
theorem kSift1 : allN 6 (fun k => sg (Nat.add 6 k)) = true := by quickRfl

theorem kQ0 : allN 4 wq = true := by quickRfl
theorem kQ1 : allN 4 (fun k => wq (Nat.add 4 k)) = true := by quickRfl
theorem kQ2 : allN 5 (fun k => wq (Nat.add 8 k)) = true := by quickRfl

end CertificateChecks.KernelLC.Fi24BQ

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.Fi24BQ.cov 0 4
#kon_join CertificateChecks.KernelLC.Fi24BQ.covAll CertificateChecks.KernelLC.Fi24BQ.cov 4
#kon_slices CertificateChecks.KernelLC.Fi24BQ.sq 0 128
#kon_join CertificateChecks.KernelLC.Fi24BQ.sqAll CertificateChecks.KernelLC.Fi24BQ.sq 128

end
