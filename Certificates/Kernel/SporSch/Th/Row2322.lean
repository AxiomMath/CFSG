
module

public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Certificates.Kernel.SporSch.ThRowsSoundBase
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.ThSchreier.RowInputs
meta import CFSG.Sporadic.ThSchreier.RowInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_v4rows CertificateChecks.KernelSporSch.ThFC CFSG.Sporadic.Th.Native.fcRows

#kss_v4rows CertificateChecks.KernelSporSch.ThFI CFSG.Sporadic.ThSchreier.formInvRows

namespace CertificateChecks.KernelSporSch.ThRow

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch

theorem bindFC : v4BindK fcRows.toList ThFC = true := by quickRfl

theorem ltFC : allN 248 (fun i => Nat.blt (ThFC i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltFI : allN 248 (fun i => Nat.blt (ThFI i) (Nat.shiftLeft 1 248)) = true := by quickRfl

theorem ab0 : idBlkK ThFC ThFI 0 31 = true := by quickRfl
theorem ab1 : idBlkK ThFC ThFI 31 31 = true := by quickRfl
theorem ab2 : idBlkK ThFC ThFI 62 31 = true := by quickRfl
theorem ab3 : idBlkK ThFC ThFI 93 31 = true := by quickRfl
theorem ab4 : idBlkK ThFC ThFI 124 31 = true := by quickRfl
theorem ab5 : idBlkK ThFC ThFI 155 31 = true := by quickRfl
theorem ab6 : idBlkK ThFC ThFI 186 31 = true := by quickRfl
theorem ab7 : idBlkK ThFC ThFI 217 31 = true := by quickRfl
theorem ba0 : idBlkK ThFI ThFC 0 31 = true := by quickRfl
theorem ba1 : idBlkK ThFI ThFC 31 31 = true := by quickRfl
theorem ba2 : idBlkK ThFI ThFC 62 31 = true := by quickRfl
theorem ba3 : idBlkK ThFI ThFC 93 31 = true := by quickRfl
theorem ba4 : idBlkK ThFI ThFC 124 31 = true := by quickRfl
theorem ba5 : idBlkK ThFI ThFC 155 31 = true := by quickRfl
theorem ba6 : idBlkK ThFI ThFC 186 31 = true := by quickRfl
theorem ba7 : idBlkK ThFI ThFC 217 31 = true := by quickRfl

theorem sh1 (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := (Nat.shiftLeft_eq 1 k).trans (Nat.one_mul _)

theorem all_of_blocks {X Y : Nat → Nat} (h0 : idBlkK X Y 0 31 = true) (h1 : idBlkK X Y 31 31 = true)
    (h2 : idBlkK X Y 62 31 = true) (h3 : idBlkK X Y 93 31 = true) (h4 : idBlkK X Y 124 31 = true)
    (h5 : idBlkK X Y 155 31 = true) (h6 : idBlkK X Y 186 31 = true)
    (h7 : idBlkK X Y 217 31 = true) : ∀ i < 248, vmT Y (X i) = 2 ^ i := by
  intro i hi
  have key : ∀ (b : Nat), idBlkK X Y b 31 = true → b ≤ i → i < b + 31 → vmT Y (X i) = 2 ^ i := by
    intro b hb h1' h2'
    have := allBlk_spec hb (i - b) (by omega)
    rw [Nat.add_eq, Nat.add_sub_cancel' h1'] at this
    rw [Nat.eq_of_beq_eq_true this, sh1]
  rcases Nat.lt_or_ge i 31 with a | a
  · exact key 0 h0 (by omega) (by omega)
  rcases Nat.lt_or_ge i 62 with b | b
  · exact key 31 h1 a (by omega)
  rcases Nat.lt_or_ge i 93 with c | c
  · exact key 62 h2 b (by omega)
  rcases Nat.lt_or_ge i 124 with d | d
  · exact key 93 h3 c (by omega)
  rcases Nat.lt_or_ge i 155 with e | e
  · exact key 124 h4 d (by omega)
  rcases Nat.lt_or_ge i 186 with f | f
  · exact key 155 h5 e (by omega)
  rcases Nat.lt_or_ge i 217 with g | g
  · exact key 186 h6 f (by omega)
  · exact key 217 h7 g (by omega)

theorem lt_of {R : Nat → Nat} (h : allN 248 (fun i => Nat.blt (R i) (Nat.shiftLeft 1 248)) = true) :
    ∀ i < 248, R i < 2 ^ 248 := fun i hi => by
  have := Nat.blt_eq.mp (allN_spec h i hi)
  rwa [sh1] at this

theorem facts : eqRows (mulRows fcRows formInvRows) idRows = true ∧
    eqRows (mulRows formInvRows fcRows) idRows = true := by
  have hab := all_of_blocks ab0 ab1 ab2 ab3 ab4 ab5 ab6 ab7
  have hba := all_of_blocks ba0 ba1 ba2 ba3 ba4 ba5 ba6 ba7
  have hfc : fcRows = rowsV ThFC := v4Bind_sound bindFC
  have hfi : formInvRows = rowsV ThFI := by
    rw [formInvRows, hfc]
    exact invRows_sound (lt_of ltFC) (lt_of ltFI) hab
  rw [hfi, hfc]
  exact ⟨mulId_sound (lt_of ltFC) (lt_of ltFI) hab, mulId_sound (lt_of ltFI) (lt_of ltFC) hba⟩

end CertificateChecks.KernelSporSch.ThRow

end
