module

public import Certificates.Kernel.SporSch.Ly.SevD2
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.UInt.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySvD

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def bpD : Array Nat := Array.ofFn (n := 826) fun i => fld(LySv.DG, 4 * i.val, 15)

@[expose] noncomputable def keyD : ByteArray := encodeDigits fun p => if p < 826 then bpD[p]! else 0

@[expose] noncomputable def uD : Array (Array Nat) :=
  Array.ofFn (n := 111) fun j => Array.ofFn (n := 7) fun m => bpD[111 * m.val + j.val]!

@[expose] noncomputable def keyF : ByteArray :=
  encodeDigits fun p => if p < 826 then fld(LySv.DG, 4 * p, 15) else 0

theorem bpD_get {i : Nat} (hi : i < 826) : bpD[i]! = fld(LySv.DG, 4 * i, 15) := by
  unfold bpD
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem keyD_eq : keyD = keyF := by
  unfold keyD keyF
  congr 1
  funext p
  split
  · rw [bpD_get (by assumption)]
  · rfl

theorem kf1 : keyF.size = 276 := by decide +kernel

theorem kf2 : ∀ q < 276, (keyF.get! q).toNat < 125 := by decide +kernel

theorem kf3 : rrefOK (keyRows keyF) #[0, 1, 2, 3, 4, 5, 6] = true := by decide +kernel

theorem kf4 : keyDigit keyF 826 = 0 ∧ keyDigit keyF 827 = 0 := by decide +kernel

theorem kf5 : ∀ j < 111, ∀ m < 7, fld(LySv.DG, 4 * (111 * m + j), 15) = keyDigit keyF (111 * m + j) := by
  decide +kernel

theorem keyFacts : keyD.size = 276 ∧ (∀ q < 276, (keyD.get! q).toNat < 125) ∧
    rrefOK (keyRows keyD) #[0, 1, 2, 3, 4, 5, 6] = true ∧ keyDigit keyD 826 = 0 ∧
    keyDigit keyD 827 = 0 ∧ ∀ j < 111, ∀ m < 7, (uD[j]!)[m]! = keyDigit keyD (111 * m + j) := by
  rw [keyD_eq]
  refine ⟨kf1, kf2, kf3, kf4.1, kf4.2, fun j hj m hm => ?_⟩
  unfold uD
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, getElem!_pos _ m (by simpa using hm),
    Array.getElem_ofFn, bpD_get (by omega)]
  exact kf5 j hj m hm

theorem rInv (j : Nat) (hj : j < 5) : mul7 LySv.RA[j]! (inv7 LySv.RA[j]!) = id7 () := by
  rw [inv_ra hj, ra_get hj, mul7_eq, (hp_get hj).2.1, id7_eq]

@[expose] noncomputable def SK : Nat := pk49 (keyS keyF)

theorem skOK : is49 (keyS keyF) SK = true := by quickRfl

theorem ckOK : allN 5 (fun j => Nat.beq (congr7K (RAP j) SK) SK) = true := by quickRfl

theorem rKey (j : Nat) (hj : j < 5) : congr7 LySv.RA[j]! (keyS keyD) = keyS keyD := by
  rw [keyD_eq, ra_get hj, dec49_of skOK, congr7_eq, Nat.eq_of_beq_eq_true (allN_spec ckOK j hj)]

end CertificateChecks.KernelSporSch.LySvD

end
