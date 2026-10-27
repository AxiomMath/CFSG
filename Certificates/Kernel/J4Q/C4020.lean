module

public import CFSG.Sporadic.J4.QTOutCocNative
public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Sporadic.J4.QTOutActNative
public import CFSG.Sporadic.J4.QTNative
public import Certificates.Kernel.J4Q.Mask
public import Certificates.Kernel.J4Q.MaskData
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.Orbits

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KD.J4Q CFSG.Sporadic.J4.QT

theorem rel_chk : decide ((∀ r ∈ rel01 ++ rel02 ++ relMix, wordT r = idT) ∧
    (∀ r ∈ rel01 ++ rel02 ++ relMix, ∀ ℓ ∈ r, ℓ ∈ letters) ∧
    (∀ r ∈ rel01, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 2 ∨ ℓ = -2) ∧
    (∀ r ∈ rel02, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 3 ∨ ℓ = -3)) = true := by
  quickRfl

@[expose] noncomputable def mkS1c (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j =>
    (rel01.all fun r => cocW (dLet 0 (32 * k + j) 0) r == 0) ==
      (32 * k + j == 0 || 32 * k + j == 1373)

#j4q_all CFSG.KD.J4Q.S1C CertificateChecks.KernelJ4Q.mkS1c 64

@[expose] noncomputable def mkS2c (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j =>
    (rel02.all fun r => cocW (dLet 0 0 (32 * k + j)) r == 0) ==
      (32 * k + j == 0 || 32 * k + j == 689)

#j4q_all CFSG.KD.J4Q.S2C CertificateChecks.KernelJ4Q.mkS2c 64

theorem stage1_eq : stage1 = [0, 1373] := by
  unfold stage1
  rw [List.filter_congr (q := fun e => e == 0 || e == 1373) fun e he => by
    have h := mkChunk (f := fun k j => (rel01.all fun r => cocW (dLet 0 (32 * k + j) 0) r == 0) ==
      (32 * k + j == 0 || 32 * k + j == 1373)) S1C.all (e := e) (by simpa using he)
    simp only [mkSplit] at h
    exact beq_iff_eq.1 h]
  exact of_decide_eq_true (by quickRfl)

theorem stage2_eq : stage2 = [0, 689] := by
  unfold stage2
  rw [List.filter_congr (q := fun e => e == 0 || e == 689) fun e he => by
    have h := mkChunk (f := fun k j => (rel02.all fun r => cocW (dLet 0 0 (32 * k + j)) r == 0) ==
      (32 * k + j == 0 || 32 * k + j == 689)) S2C.all (e := e) (by simpa using he)
    simp only [mkSplit] at h
    exact beq_iff_eq.1 h]
  exact of_decide_eq_true (by quickRfl)

theorem relAll_chk : decide (relAll 0 0 = true ∧ relAll 1373 689 = true ∧ relAll 0 689 = false ∧
    relAll 1373 0 = false) = true := by
  quickRfl

@[expose] noncomputable def mkPrec (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j => decide (mkPre.getD (32 * k + j) 0 < 2048 ∧
    mkPre.getD (32 * k + j) 0 ^^^ actT (letterTab 1) (mkPre.getD (32 * k + j) 0) = 32 * k + j)

#j4q_all CFSG.KD.J4Q.PRC CertificateChecks.KernelJ4Q.mkPrec 64

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem c4020 : (∀ r ∈ rel01 ++ rel02 ++ relMix, wordT r = idT)
    ∧ (∀ r ∈ rel01 ++ rel02 ++ relMix, ∀ ℓ ∈ r, ℓ ∈ letters)
    ∧ (∀ r ∈ rel01, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 2 ∨ ℓ = -2)
    ∧ (∀ r ∈ rel02, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 3 ∨ ℓ = -3)
    ∧ (stage1 = [0, 1373])
    ∧ (stage2 = [0, 689])
    ∧ (relAll 0 0 = true ∧ relAll 1373 689 = true ∧ relAll 0 689 = false ∧
          relAll 1373 0 = false)
    ∧ (∀ e < 2 ^ 11, ∃ v < 2 ^ 11, v ^^^ actT (letterTab 1) v = e) := by
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true rel_chk
  refine ⟨h1, h2, h3, h4, stage1_eq, stage2_eq, of_decide_eq_true relAll_chk, fun e he => ?_⟩
  have he' : e < 32 * 64 := by simpa using he
  have h := mkChunk (f := fun k j => decide (mkPre.getD (32 * k + j) 0 < 2048 ∧
    mkPre.getD (32 * k + j) 0 ^^^ actT (letterTab 1) (mkPre.getD (32 * k + j) 0) = 32 * k + j))
    PRC.all he'
  simp only [mkSplit] at h
  obtain ⟨hv, hx⟩ := of_decide_eq_true h
  exact ⟨mkPre.getD e 0, by simpa using hv, hx⟩

end CertificateChecks.KernelJ4Q

end
