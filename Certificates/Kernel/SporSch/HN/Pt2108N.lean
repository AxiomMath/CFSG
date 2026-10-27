
module

public import CFSG.Sporadic.HNSchreier.SylowCheckInputs
public import CFSG.Certificates.Kernel.SporSch.HNF5RankSound
public import CFSG.Certificates.Kernel.SporSch.HNNat
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2108N

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.He CertificateChecks.KernelSporSch CFSG.KS.TW CFSG.KS

theorem letters_H : ∀ c < 48, ∀ l ∈ FAData.wHWord[c]!, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide +kernel

@[expose] def trip (k y : ℕ) : ℕ := if y < 3 * k then (if y % 3 = 2 then y - 2 else y + 1) else y

theorem nat_facts : ∀ c < 48, (natArr SylowData.rho[c]!).size = 12 ∧
    (∀ x < 12, FAData.wHWord[c]!.foldr (GZ HNNat.natF HNNat.natFI) x =
      (natArr FAData.wNat[c]!)[x]!) ∧
    (∀ x < 12, (natArr SylowData.rho[c]!)[x]! < 12 ∧
      SylowData.rho[c]!.idxOf ((natArr SylowData.rho[c]!)[x]!) = x) ∧
    (∀ x < 12, SylowData.rho[c]!.idxOf x < 12 ∧
      trip FAData.wCycles[c]! (SylowData.rho[c]!.idxOf x) < 12 ∧
      (natArr SylowData.rho[c]!)[trip FAData.wCycles[c]! (SylowData.rho[c]!.idxOf x)]! =
        (natArr FAData.wNat[c]!)[x]!) := by
  decide +kernel

theorem pinv_rho {c : ℕ} (hc : c < 48) {y : ℕ} (hy : y < 12) :
    (pinvCand 12 (natArr SylowData.rho[c]!))[y]! = SylowData.rho[c]!.idxOf y := by
  obtain ⟨hs, -, hr, -⟩ := nat_facts c hc
  have e : natArr SylowData.rho[c]! = Array.ofFn (n := 12) fun i =>
      (natArr SylowData.rho[c]!)[i.val]! := CFSG.KS.PW.arr_ext hs fun _ _ => rfl
  rw [e]
  exact CFSG.KS.CB.pinvCand_get (T := fun x => (natArr SylowData.rho[c]!)[x]!)
    (U := fun y => SylowData.rho[c]!.idxOf y)
    (fun x hx => (hr x hx).1) (fun x hx => (hr x hx).2) hy

theorem nat_w {c : ℕ} (hc : c < 48) :
    peq 12 (pword 12 HNNat.natS (pinvs 12 HNNat.natS) FAData.wHWord[c]!)
      (natArr FAData.wNat[c]!) = true :=
  HNNat.peq_maps fun x hx => by
    rw [HNNat.natWord_pt (letters_H c hc) hx, (nat_facts c hc).2.1 x hx]

theorem nat_inv {c : ℕ} (hc : c < 48) :
    pisInv 12 (natArr SylowData.rho[c]!) (pinvCand 12 (natArr SylowData.rho[c]!)) = true := by
  refine CFSG.ONSchreier.allBelowN_iff.2 fun x hx => ?_
  obtain ⟨-, -, hr, -⟩ := nat_facts c hc
  rw [pinv_rho hc (hr x hx).1, (hr x hx).2]
  simp [(hr x hx).1]

theorem tripleArr_get {k y : ℕ} (hy : y < 12) : (tripleArr k)[y]! = trip k y := by
  rw [tripleArr, getElem!_pos _ y (by simpa using hy), Array.getElem_ofFn]
  rfl

theorem nat_conj {c : ℕ} (hc : c < 48) :
    peq 12 (pcomp 12 (pcomp 12 (natArr SylowData.rho[c]!) (tripleArr FAData.wCycles[c]!))
      (pinvCand 12 (natArr SylowData.rho[c]!))) (natArr FAData.wNat[c]!) = true :=
  HNNat.peq_maps fun x hx => by
    obtain ⟨-, -, -, ht⟩ := nat_facts c hc
    obtain ⟨h1, h2, h3⟩ := ht x hx
    rw [CFSG.KS.PW.pcomp_get' hx, pinv_rho hc hx, CFSG.KS.PW.pcomp_get' h1, tripleArr_get h1, h3]

end CertificateChecks.KernelSporSch.HNPt2108N

end
