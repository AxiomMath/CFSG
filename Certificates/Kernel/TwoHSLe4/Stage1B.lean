module

public import Certificates.Kernel.TwoHSLe4.SO5D
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.PCountSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem contains_memB (x : ℕ) (L : List ℕ) : L.contains x = CFSG.KS.PCnt.memB x L := by
  rw [Bool.eq_iff_iff, CFSG.KS.PCnt.memB_iff]
  simp

@[expose] noncomputable def bRow (p : ℕ) : Bool :=
  P0L.all fun q => CFSG.KS.PCnt.memB (mulK p q) P0L

@[expose] noncomputable def bS (s : ℕ) : Bool :=
  CFSG.KC.Enum.allN 32 (fun d => bRow (P0 (Nat.add (Nat.mul 32 s) d)))

end CertificateChecks.KernelTwoHSLe4.SO5

#kc_each CertificateChecks.KernelTwoHSLe4.SO5.bS 0 4

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem b_mul : P0L.all (fun p => P0L.all fun q => P0L.contains (mulK p q)) = true := by
  simp only [contains_memB]
  change P0L.all bRow = true
  rw [List.all_eq_true]
  intro p hp
  unfold P0L at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  have hi' : i < 128 := List.mem_range.1 hi
  have hs : bS (i / 32) = true := by
    rcases (by omega : i / 32 = 0 ∨ i / 32 = 1 ∨ i / 32 = 2 ∨ i / 32 = 3) with h | h | h | h <;>
      rw [h]
    exacts [bS0, bS1, bS2, bS3]
  have h := CFSG.KS.allN_spec hs (i % 32) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 32 (i / 32)) (i % 32) = i := Nat.div_add_mod i 32
  simp only [e] at h
  exact h

theorem b_inv : P0L.all (fun p => P0L.any fun q => mulK p q == oneK) = true := by quickRfl

theorem b_inv2 : P0L.all (fun p => !(mulK p p == oneK) || decide (unpk p = fmOne) ||
    CJL.any fun e => e.1 == p) = true := by
  quickRfl

theorem b_cj : CJL.all (fun e => P0L.contains e.1 && mulK e.2.1 e.1 == mulK (SG (e.2.2 % 4)) e.2.1) =
    true := by
  quickRfl

theorem b_tau3 : P0L.all (fun p => mulK p (SG 2) == mulK (SG 2) p) = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.SO5

end
