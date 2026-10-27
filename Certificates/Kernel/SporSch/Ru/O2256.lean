
module

public import Certificates.Kernel.SporSch.Ru.C2253
public import Certificates.Data.Kernel.SporSch.RuOrbK
meta import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuOr

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def bfsQueue (n : Nat) (gens : Array (Array Nat)) (roots : Array Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for r in roots do
    if r < n && !seen[r]! then
      seen := seen.set! r true
      queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:gens.size] do
        let y := (gens[k]!)[x]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          queue := queue.push y
  return queue

meta def invList (n : Nat) (q : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for t in [0:q.size] do
    r := r.set! q[t]! t
  return r

meta def events (R : Nat) (q par gl : Array Nat) : Array Nat :=
  let ord := invList q.size q
  (Array.range q.size).map fun t => if t < R then 0 else 2 * ord[par[q[t]!]!]! + gl[q[t]!]!

meta def ocM : Array (Array Nat) := ruCOrbits.toArray
meta def onM : Array (Array Nat) := ruNOrbits.toArray
meta def ocpM : Array (Array Nat) := ruCOrbitPos.toArray
meta def onpM : Array (Array Nat) := ruNOrbitPos.toArray
meta def labCM : Array Nat := ruCLab
meta def labNM : Array Nat := ruNLab
meta def depCM : Array Nat := ruCForest.1
meta def parCM : Array Nat := ruCForest.2.1
meta def glCM : Array Nat := ruCForest.2.2
meta def depNM : Array Nat := ruNForest.1
meta def parNM : Array Nat := ruNForest.2.1
meta def glNM : Array Nat := ruNForest.2.2
meta def qCM : Array Nat := bfsQueue 4060 #[ruC0A, ruC1A] ruCRoots
meta def qNM : Array Nat := bfsQueue 4060 #[ruNs0A, ruNs1A] ruNRoots
meta def ordCM : Array Nat := invList 4060 qCM
meta def ordNM : Array Nat := invList 4060 qNM
meta def foCM : Array Nat := events 4 qCM parCM glCM
meta def foNM : Array Nat := events 3 qNM parNM glNM

end CertificateChecks.KernelSporSch.RuOr

#kss_perms CertificateChecks.KernelSporSch.RuOr.OC 12 CertificateChecks.KernelSporSch.RuOr.ocM
#kss_perms CertificateChecks.KernelSporSch.RuOr.ON 12 CertificateChecks.KernelSporSch.RuOr.onM
#kss_perms CertificateChecks.KernelSporSch.RuOr.OCP 12 CertificateChecks.KernelSporSch.RuOr.ocpM
#kss_perms CertificateChecks.KernelSporSch.RuOr.ONP 12 CertificateChecks.KernelSporSch.RuOr.onpM
#ks_perm CertificateChecks.KernelSporSch.RuOr.LABC 12 CertificateChecks.KernelSporSch.RuOr.labCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.LABN 12 CertificateChecks.KernelSporSch.RuOr.labNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.DEPC 12 CertificateChecks.KernelSporSch.RuOr.depCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.PARC 12 CertificateChecks.KernelSporSch.RuOr.parCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.GLC 12 CertificateChecks.KernelSporSch.RuOr.glCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.DEPN 12 CertificateChecks.KernelSporSch.RuOr.depNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.PARN 12 CertificateChecks.KernelSporSch.RuOr.parNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.GLN 12 CertificateChecks.KernelSporSch.RuOr.glNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.QC 12 CertificateChecks.KernelSporSch.RuOr.qCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.QN 12 CertificateChecks.KernelSporSch.RuOr.qNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.ORDC 12 CertificateChecks.KernelSporSch.RuOr.ordCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.ORDN 12 CertificateChecks.KernelSporSch.RuOr.ordNM
#ks_perm CertificateChecks.KernelSporSch.RuOr.FOC 13 CertificateChecks.KernelSporSch.RuOr.foCM
#ks_perm CertificateChecks.KernelSporSch.RuOr.FON 13 CertificateChecks.KernelSporSch.RuOr.foNM

namespace CertificateChecks.KernelSporSch.RuOr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def stC (k : Nat) : Nat := List.getD [0, 1920, 3968, 4048] k 0

@[expose] noncomputable def szC (k : Nat) : Nat := List.getD [1920, 2048, 80, 12] k 0

@[expose] noncomputable def stN (k : Nat) : Nat := List.getD [4060, 7644, 8092] k 0

@[expose] noncomputable def szN (k : Nat) : Nat := List.getD [3584, 448, 28] k 0

theorem ocK : allN 4 (fun k => hexPackK 3 4060 10120 (stC k) (szC k) 12 (OC k) RuPts.chars) =
    true := by quickRfl
theorem onK : allN 3 (fun k => hexPackK 3 4060 10120 (stN k) (szN k) 12 (ON k) RuPts.chars) =
    true := by quickRfl
theorem ocpK : allN 4 (fun k => posK 4060 (szC k) 12 (OC k) (OCP k)) = true := by quickRfl
theorem onpK : allN 3 (fun k => posK 4060 (szN k) 12 (ON k) (ONP k)) = true := by quickRfl
theorem labCK : labK 4060 12 4 OC szC OCP LABC = true := by quickRfl
theorem labNK : labK 4060 12 3 ON szN ONP LABN = true := by quickRfl
theorem fC : allN 4060 (forestAt 4060 12 13 4 C0 C1 QC ORDC FOC DEPC PARC GLC) = true := by quickRfl
theorem fN : allN 4060 (forestAt 4060 12 13 3 Ns0 Ns1 QN ORDN FON DEPN PARN GLN) = true := by
  quickRfl
theorem eC : allN 8120 (eventAt 4060 12 13 4 C0 C1 QC ORDC FOC) = true := by quickRfl
theorem eN : allN 8120 (eventAt 4060 12 13 3 Ns0 Ns1 QN ORDN FON) = true := by quickRfl
theorem pC : allN 4060 (partAt 4060 12 4 C0 C1 LABC QC DEPC PARC GLC) = true := by quickRfl
theorem pN : allN 4060 (partAt 4060 12 3 Ns0 Ns1 LABN QN DEPN PARN GLN) = true := by quickRfl
theorem rC : allN 4 (rootAt 4060 12 LABC QC) = true := by quickRfl
theorem rN : allN 3 (rootAt 4060 12 LABN QN) = true := by quickRfl
theorem rootsC : allN 4 (fun t => Nat.beq (pg 12 (mask 12) QC t) (pg 12 (mask 12) (OC t) 0)) =
    true := by quickRfl
theorem rootsN : allN 3 (fun t => Nat.beq (pg 12 (mask 12) QN t) (pg 12 (mask 12) (ON t) 0)) =
    true := by quickRfl
theorem fOC : Nat.beq (OC 0) RuF.F = true := by quickRfl
theorem yOC : Nat.beq (OC 2) RuCe.Y = true := by quickRfl

end CertificateChecks.KernelSporSch.RuOr

end
