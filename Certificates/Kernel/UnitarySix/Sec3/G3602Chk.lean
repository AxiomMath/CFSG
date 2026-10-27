module

public import Certificates.Kernel.UnitarySix.Sec3.E3600Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3YElt
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def ptW (w : List ℕ) (p : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) p (fun k _ ih => pg 10 (mask 10) (sec3G k) ih) w

@[expose] noncomputable def key3W (w : List ℕ) : ℕ :=
  Nat.add (ptW w 45) (Nat.mul 1024 (Nat.add (ptW w 3) (Nat.mul 1024 (ptW w 1))))

@[expose] noncomputable def keyA3W (w : List ℕ) : ℕ :=
  Nat.add (Nat.mul (ptW w 205) 1024) (ptW w 251)

theorem kKeys : (a2Tab.map (fun p => key3W (cjW p.1 a2Reps[p.2]!)) == a2Keys &&
    a1Tab.map (fun p => ptW (cjW p.1 a1Reps[p.2]!) 1) == a1Keys &&
    a1Tab.map (fun p => ptW (cjW p.1 a1Reps[p.2]! ++ [14]) 1) == a1KeysZ &&
    a3Tab.map (fun p => keyA3W (cjW p.1 a3Reps[p.2]!)) == a3Keys &&
    singReps.map (fun s => ptW s 1) == singKeys &&
    singReps.map (fun s => ptW (s ++ [14]) 1) == singKeysZ) = true := by
  decide +kernel

theorem tabs_lt : (∀ p ∈ a2Tab, ∀ k ∈ cjW p.1 a2Reps[p.2]!, k < 18) ∧
    (∀ p ∈ a1Tab, ∀ k ∈ cjW p.1 a1Reps[p.2]! ++ [14], k < 18) ∧
    (∀ p ∈ a3Tab, ∀ k ∈ cjW p.1 a3Reps[p.2]!, k < 18) ∧
    (∀ s ∈ singReps, ∀ k ∈ s ++ [14], k < 18) ∧ (∀ s ∈ singReps, ∀ k ∈ s ++ s, k < 18) := by
  decide +kernel

theorem kReps : (ptW (a1Reps[0]! ++ a1Reps[0]!) 1 == 1 &&
    ptW (a1Reps[1]! ++ a1Reps[1]!) 1 == pg 10 (mask 10) (sec3G 14) 1) = true := by
  decide +kernel

theorem kSing : (singReps.all fun s => ptW (s ++ s) 1 == 1) = true := by decide +kernel

theorem kSingNodup : (singKeys ++ singKeysZ).Nodup := by decide +kernel

theorem zCls_lt' : (∀ c ∈ zCls, ∀ k ∈ c, k < 18) ∧
    ∀ j < 20, (∀ k ∈ zMs[j]! ++ [14], k < 18) ∧ (∀ k ∈ [14] ++ zMs[j]!, k < 18) ∧
      (∀ k ∈ cjW zMs[j]! zCls[1]!, k < 18) ∧ ∀ k ∈ zCls[j + 1]!, k < 18 := by
  decide +kernel

@[expose] noncomputable def forceL (L : List ℕ) : List ℕ → (List ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => List ℕ → (List ℕ → Bool) → Bool) (fun acc k => k acc)
    (fun h _ ih acc k => strictB h fun h' => ih (h' :: acc) k) L

@[expose] noncomputable def zConjK (ZP : List ℕ) : Bool :=
  (List.range chK2.gens.length).all fun j => ZP.all fun C =>
    strictB (pcomp 693 10 (mask 10) (CK2.S j) (pcomp 693 10 (mask 10) C (CK2.SI j)))
      fun X => ZP.any fun C' => Nat.beq X C'

theorem kZC1 : forceL (zCls.map wK) [] zConjK = true := by quickRfl

theorem kZC2 : ((List.range 10).all fun j =>
    Nat.beq (wK (zMs[j]! ++ [14])) (wK ([14] ++ zMs[j]!)) &&
      Nat.beq (wK (cjW zMs[j]! zCls[1]!)) (wK zCls[j + 1]!)) = true := by
  decide +kernel

theorem kZC3 : ((List.range 10).all fun j =>
    Nat.beq (wK (zMs[j + 10]! ++ [14])) (wK ([14] ++ zMs[j + 10]!)) &&
      Nat.beq (wK (cjW zMs[j + 10]! zCls[1]!)) (wK zCls[j + 10 + 1]!)) = true := by
  decide +kernel

end CertificateChecks.KernelU6.Sec3
