module

public import Certificates.Kernel.SporSch.Co1.CRows
public import CFSG.Sporadic.Schreier.Co1GenCheckInputs
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenQTowerB
public import Certificates.Data.Kernel.SporSch.Co1GenB
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1GenCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenQTowerB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Gen

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native

meta def TTA : Array (Array (Nat × Nat × Nat)) := Array.ofFn (n := 7) fun i => towerTree i.val

meta def EAA : Array (Array Nat) := Array.ofFn (n := 7) fun i => Id.run do
  let t := towerTree i.val
  let pos : Std.HashMap Nat Nat := (List.range t.size).foldl (fun m k => m.insert t[k]!.1 k) {}
  let mut es : Array Nat := #[]
  for h in [0:t.size] do
    for g in towerJ i.val do
      es := es.push (pos.getD (stepV (towerQ i.val) g t[h]!.1) t.size)
  return es

meta def actRows (R : Array Nat) (v : Nat) : Nat :=
  (List.range 24).foldl (fun s i =>
    if (List.range 24).foldl (fun p j => p ^^ ((R[i]?.getD 0) &&& v).testBit j) false
    then s ||| (1 <<< i) else s) 0

meta def BTA : Array Nat := Array.ofFn (n := 93) fun j =>
  let R := (extDag.1[j.val]?).getD #[]
  (List.range 96).foldl (fun acc e => acc ||| (actRows R ((e % 16) <<< (4 * (e / 16))) <<< (24 * e))) 0

end CertificateChecks.KernelSporSch.Co1Gen

#kss_co1dag CertificateChecks.KernelSporSch.Co1Gen.ED CFSG.Sporadic.Co1Schreier.Native.extDag
#kss_co1qtowerB CertificateChecks.KernelSporSch.Co1Gen.TW CertificateChecks.KernelSporSch.Co1Gen.TTA
  CertificateChecks.KernelSporSch.Co1Gen.EAA CFSG.Sporadic.Co1Schreier.Data.towerQuot
  CFSG.Sporadic.Co1Schreier.Data.towerGens CertificateChecks.KernelSporSch.Co1Gen.BTA
  CertificateChecks.KernelSporSch.Co1Gen.ED.M 93 512

namespace CertificateChecks.KernelSporSch.Co1Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CertificateChecks.KernelSporSch.Co1Elem
open CertificateChecks.KernelSporSch.Co1Split CertificateChecks.KernelSporSch.Co1ThreeLocal

@[expose] noncomputable def EI (i : Nat) : Nat :=
  nIf(Nat.blt i 6, AF i, nIf(Nat.beq i 6, CRP 0, nIf(Nat.beq i 7, CRP 1,
    nIf(Nat.beq i 8, GF 2, XP 0))))

theorem kEI : allN 10 (fun i => Nat.beq (ED.M i) (EI i)) = true := by quickRfl
theorem kD : dagIK ED.M ED.MI 10 ED.N Data.genDerivs = true := by quickRfl
theorem kN : Nat.beq ED.N 93 = true := by quickRfl

theorem tbNeg : bIf(tabOK (ED.M 0) (Nat.xor (TW.B 0) 1), false, true) = true := by quickRfl

theorem fq0 : fixQK ED.M (Data.towerGens.getD 0 []) Data.towerQuot Data.towerBase 0 = true := by
  quickRfl
theorem fq1 : fixQK ED.M (Data.towerGens.getD 1 []) Data.towerQuot Data.towerBase 1 = true := by
  quickRfl
theorem fq2 : fixQK ED.M (Data.towerGens.getD 2 []) Data.towerQuot Data.towerBase 2 = true := by
  quickRfl
theorem fq3 : fixQK ED.M (Data.towerGens.getD 3 []) Data.towerQuot Data.towerBase 3 = true := by
  quickRfl
theorem fq4 : fixQK ED.M (Data.towerGens.getD 4 []) Data.towerQuot Data.towerBase 4 = true := by
  quickRfl
theorem fq5 : fixQK ED.M (Data.towerGens.getD 5 []) Data.towerQuot Data.towerBase 5 = true := by
  quickRfl
theorem fq6 : fixQK ED.M (Data.towerGens.getD 6 []) Data.towerQuot Data.towerBase 6 = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co1Gen

end
