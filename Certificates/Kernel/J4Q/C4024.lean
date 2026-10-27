module

public import CFSG.Sporadic.J4.QTRankNative
public import Certificates.Kernel.J4Q.MaskBlk
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT

@[expose] noncomputable def mkKey (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add x (Nat.mul (nat_lit 2048) ih)) t

theorem mkKey_chk : mkNodup (mkTL.map fun t => Nat.mod (mkKey t) 52242) = true := by quickRfl

@[expose] noncomputable def mkCL (k j : Nat) : Bool := CFSG.KC.Enum.allN 4 fun i =>
    Nat.blt (getN 0 (getL mkCAB k) (4 * j + i)) 1024 &&
    compN (tabAt (32 * k + j)) (getL mkKT i) == tabAt (getN 0 (getL mkCAB k) (4 * j + i)) &&
    Nat.blt (getN 0 (getL mkCBB k) (4 * j + i)) 1024 &&
    compN (tabAt (32 * k + j)) (getL mkKIT i) == tabAt (getN 0 (getL mkCBB k) (4 * j + i))

@[expose] noncomputable def mkCLc (k : Nat) : Bool := CFSG.KC.Enum.allN 32 (mkCL k)

#j4q_all CFSG.KD.J4Q.CLC CertificateChecks.KernelJ4Q.mkCLc 32

@[expose] noncomputable def mkFX (k j : Nat) : Bool :=
  !(compN (tabAt (32 * k + j)) (tabAt (32 * k + j)) == idT) ||
    tabAt (32 * k + j) == idT || Nat.ble (fixN (tabAt (32 * k + j))) 128

@[expose] noncomputable def mkFXc (k : Nat) : Bool := CFSG.KC.Enum.allN 32 (mkFX k)

#j4q_all CFSG.KD.J4Q.FXC CertificateChecks.KernelJ4Q.mkFXc 32

theorem lenOK_chk : decide (∀ t ∈ mkTL, lenOK t = true) = true := by quickRfl

theorem lenK_chk : decide (∀ i ∈ List.range 4, lenOK (mkKT.getD i []) = true ∧
    lenOK (mkKIT.getD i []) = true) = true := by quickRfl

theorem letters_chk : decide (∀ i ∈ List.range 4, ∀ ℓ ∈ mkKW.getD i [], ℓ ∈ letters) = true := by
  quickRfl

theorem letterTab_chk : decide (∀ ℓ ∈ letters, lenOK (letterTab ℓ) = true) = true := by quickRfl

theorem idT_chk : decide (mkTL.getD 0 [] = idT) = true := by quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem c4024 : (tabL.Nodup)
    ∧ (∀ t ∈ tabL, lenOK t = true)
    ∧ (idT ∈ tabL)
    ∧ (∀ t ∈ tabL, ∀ i < 4,
          compT t (kTab i) ∈ tabL ∧ compT t (kInvTab i) ∈ tabL)
    ∧ (∀ i < 4, lenOK (kTab i) = true ∧ lenOK (kInvTab i) = true)
    ∧ (∀ t ∈ tabL, compT t t = idT → t ≠ idT → fixCount t ≤ 128)
    ∧ (tabL.length = 1024)
    ∧ (∀ i < 4, ∀ ℓ ∈ kWords.getD i [], ℓ ∈ letters)
    ∧ (∀ ℓ ∈ letters, lenOK (letterTab ℓ) = true)
    ∧ (∀ e < 1024, ∀ i ∈ pcSeq e, i < 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, of_decide_eq_true letterTab_chk, pcSeq_lt⟩
  · rw [tabL_eq]
    exact ((nodup_of_mkNodup mkKey_chk).of_map _)
  · rw [tabL_eq]
    exact of_decide_eq_true lenOK_chk
  · rw [tabL_eq, ← of_decide_eq_true idT_chk]
    exact getD_mem_mkTL (by decide)
  · rw [tabL_eq]
    intro t ht i hi
    obtain ⟨e, he, rfl⟩ := mem_mkTL ht
    have h := CFSG.KS.allN_spec (mkChunkW (w := 32) (n := 32) (f := mkCL) CLC.all (e := e) he) i hi
    simp only [mkSplitW, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨ha, ea⟩, hb⟩, eb⟩ := h
    generalize getN 0 (getL mkCAB (e / 32)) (4 * (e % 32) + i) = a at ha ea
    generalize getN 0 (getL mkCBB (e / 32)) (4 * (e % 32) + i) = b at hb eb
    have ha' := mkLt ha
    have hb' := mkLt hb
    rw [tabAt_eq he, tabAt_eq ha', getL_eq] at ea
    rw [tabAt_eq he, tabAt_eq hb', getL_eq] at eb
    rw [kTab_eq hi, kInvTab_eq hi, compT_eq, compT_eq, ea, eb]
    exact ⟨getD_mem_mkTL ha', getD_mem_mkTL hb'⟩
  · intro i hi
    rw [kTab_eq hi, kInvTab_eq hi]
    exact (of_decide_eq_true lenK_chk) i (List.mem_range.2 hi)
  · rw [tabL_eq]
    intro t ht h1 h2
    obtain ⟨e, he, rfl⟩ := mem_mkTL ht
    have h := mkChunkW (w := 32) (n := 32) (f := mkFX) FXC.all (e := e) (by omega)
    unfold mkFX at h
    simp only [mkSplitW, tabAt_eq he, ← compT_eq, h1, h2, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq,
      Bool.or_eq_true, false_or] at h
    rw [fixCount_eq]
    exact Nat.le_of_ble_eq_true h
  · rw [tabL_eq, mkTL_length]
  · rw [kWords_eq]
    exact fun i hi => of_decide_eq_true letters_chk i (List.mem_range.2 hi)

end CertificateChecks.KernelJ4Q

end
