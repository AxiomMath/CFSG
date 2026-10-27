module

public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Orders.Co1.Checks.D
import CFSG.Certificates.Kernel.Orders.Co1.Checks.K
import CFSG.Certificates.Kernel.Orders.Co1.Data.Sel
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Data.CFSGNative.Co1Schreier.Base
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Co1SeedA CFSG.Sporadic.Co1.Native.seedA

#ks_chars CertificateChecks.KernelSporSch.Co1SeedB CFSG.Sporadic.Co1.Native.seedB

namespace CertificateChecks.KernelSporSch.Co1Rows

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.KS.Ord

@[expose] def RA : Array Nat := #[14568742, 8730514, 16056698, 3053411, 7222122, 11550909,
  6184221, 8477716, 11437002, 10461699, 6969765, 13973477, 1322595, 15457769, 1328873, 13337339,
  10191992, 3643281, 15394642, 8995024, 9732588, 6652923, 12246250, 12562466]

@[expose] def RB : Array Nat := #[6360623, 14740635, 11798632, 6366879, 7578691, 12993865,
  16345908, 15448472, 7321200, 2745588, 9841156, 1296923, 6426820, 2765237, 12296090, 4376699,
  12707437, 5432847, 14747083, 16526157, 2229586, 2736718, 1418073, 12866597]

private theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK Co1SeedA.chars CFSG.KD.OrdCo1.P1 256 621 = true := by
  quickRfl

private theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK Co1SeedB.chars CFSG.KD.OrdCo1.P2 256 621 = true := by
  quickRfl

private theorem decA : CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Sporadic.Co1.Native.seedA =
    ordMat 2 24 6 144 (CFSG.KD.OrdCo1.RW 1) := by
  rw [Co1SeedA.eq]
  exact seed_sound (hnb := rfl) CFSG.KD.OrdCo1.consts seed1_bytes (by decide)
    CFSG.KD.OrdCo1.d1_0 CFSG.KD.OrdCo1.d1_end

private theorem decB : CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Sporadic.Co1.Native.seedB =
    ordMat 2 24 6 144 (CFSG.KD.OrdCo1.RW 2) := by
  rw [Co1SeedB.eq]
  exact seed_sound (hnb := rfl) CFSG.KD.OrdCo1.consts seed2_bytes (by decide)
    CFSG.KD.OrdCo1.d2_0 CFSG.KD.OrdCo1.d2_end

theorem natCast_zmod_two (n : ℕ) : (n : ZMod 2) = if (n % 2 == 1) = true then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem mat_of_bits {R : Array Nat} {M : Nat} (hR : R.size = 24)
    (h : ∀ i < 24, ∀ j < 24,
      R[i]!.testBit j = (M / 2 ^ (144 * i + 6 * j) % 2 ^ 6 % 2 == 1)) :
    rowsMatrix 24 R = ordMat 2 24 6 144 M := by
  ext i j
  rw [rowsMatrix_apply, Array.getElem?_eq_getElem (by rw [hR]; exact i.2), Option.getD_some]
  unfold ordMat toVecD
  rw [natCast_zmod_two, ← h i i.2 j j.2, getElem!_pos R (i : ℕ) (by rw [hR]; exact i.2)]

private theorem bitsA : ∀ i < 24, ∀ j < 24, RA[i]!.testBit j =
    (CFSG.KD.OrdCo1.RW 1 / 2 ^ (144 * i + 6 * j) % 2 ^ 6 % 2 == 1) := by
  decide +kernel

private theorem bitsB : ∀ i < 24, ∀ j < 24, RB[i]!.testBit j =
    (CFSG.KD.OrdCo1.RW 2 / 2 ^ (144 * i + 6 * j) % 2 ^ 6 % 2 == 1) := by
  decide +kernel

theorem rows_eq_of_mat {R R' : Array Nat} (hR : R.size = 24) (hR' : R'.size = 24)
    (hl : ∀ i < 24, R[i]! < 2 ^ 24) (hl' : ∀ i < 24, R'[i]! < 2 ^ 24)
    (h : rowsMatrix 24 R = rowsMatrix 24 R') : R = R' := by
  apply Array.ext (hR.trans hR'.symm)
  intro i h1 h2
  have hi : i < 24 := hR ▸ h1
  have e := congrFun (congrFun h ⟨i, hi⟩)
  have e' : toVecD 24 (R[i]?.getD 0) = toVecD 24 (R'[i]?.getD 0) := funext fun j => e j
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at e'
  have b := hl i hi
  have b' := hl' i hi
  rw [getElem!_pos R i h1] at b
  rw [getElem!_pos R' i h2] at b'
  exact toVecD_injective b b' e'

theorem payload_facts (s : String) : (rowsOfPayload 24 s).size = 24 ∧
    ∀ i < 24, (rowsOfPayload 24 s)[i]! < 2 ^ 24 := by
  refine ⟨by unfold rowsOfPayload; simp, fun i hi => ?_⟩
  unfold rowsOfPayload
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact ofBits_lt 24 _

theorem rowsA_eq : CFSG.Sporadic.Co1.Native.co1Data.rowsA = RA := by
  have hm : rowsMatrix 24 (rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedA) =
      rowsMatrix 24 RA := by
    rw [rowsMatrix_rowsOfPayload, decA, mat_of_bits rfl bitsA]
  exact rows_eq_of_mat (payload_facts _).1 rfl (payload_facts _).2 (by decide) hm

theorem rowsB_eq : CFSG.Sporadic.Co1.Native.co1Data.rowsB = RB := by
  have hm : rowsMatrix 24 (rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedB) =
      rowsMatrix 24 RB := by
    rw [rowsMatrix_rowsOfPayload, decB, mat_of_bits rfl bitsB]
  exact rows_eq_of_mat (payload_facts _).1 rfl (payload_facts _).2 (by decide) hm

end CertificateChecks.KernelSporSch.Co1Rows

end
