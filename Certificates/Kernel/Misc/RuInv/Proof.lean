module

public import Certificates.Kernel.Misc.RuInv.Check
public import Certificates.Kernel.Misc.RuInv.Blocks
public import Certificates.Kernel.Misc.RuInv.HashBlocks
public import Certificates.Kernel.Misc.RuInv.CovBlocks
public import Certificates.Kernel.Misc.RuInv.PermA
public import CFSG.Certificates.Kernel.Misc.RuInvSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.KC.Misc.RuInv
  CFSG.EvenSporadicStandard.RuStd CertificateChecks.KernelMisc.RuSq
  CertificateChecks.KernelMisc.TextBlocks

theorem row_eq {j P : Nat} (hj : j < 39)
    (hk : lineK 3 4060 12 P (RuSqT.chars.drop (j * (3 * 4060 + 1))) = true) :
    ruArr4060 j = unpack 4060 12 P := by
  have ha : asciiK (RuSqT.chars.take ((j + 1) * (3 * 4060 + 1))) = true :=
    asciiK_take (by omega) asciiOK
  have hl := lineK_sound ha hk
  unfold ruArr4060 ruHexRow ruBytes4060 ruHexAt
  rw [RuSqT.eq]
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa using h1)

theorem hA0 : ruArr4060 0 = unpack 4060 12 AD.n0 := row_eq (by omega) line0

theorem hA1 : ruArr4060 1 = unpack 4060 12 AD.n1 := row_eq (by omega) line1

theorem hslot : slotK cprogK AD.n0 AD.n1 = (AD.n2, AD.n3) := by
  have h := slotOK
  rw [Bool.and_eq_true] at h
  exact Prod.ext (Nat.eq_of_beq_eq_true h.1) (Nat.eq_of_beq_eq_true h.2)

open Certificates in
theorem cert24930 : CFSG.EvenSporadicStandard.RuStd.ruInvCheck = true := by
  have hconj : ∀ j < 16 * 87, conjE E G GI NX.n0 j = true := forall_of_blocks conjAll
  have hhash : ∀ j < 16 * 87, hashE E HS j = true := forall_of_blocks hashAll
  have hcov : ∀ a < 32 * 64, covA KernelMisc.RuSqS.LR KernelMisc.RuSqS.TR E VH a = true :=
    forall_of_blocks covAll
  exact ruInvK_sound hA0 hA1 permA0 permA1 hslot perm0 perm1 hz hw1 hw2 hw3 hw4
    (fun j hj => hconj j (by omega)) ⟨reach0, reach1, reach2, reach3, reach4⟩
    (fun j hj => hhash j (by omega)) keysOK
    KernelMisc.RuSq.bindsSq KernelMisc.RuSq.permS KernelMisc.RuSqS.hl
    ⟨Nat.eq_of_beq_eq_true cnt0, Nat.eq_of_beq_eq_true cnt1⟩ (fun a ha => hcov a (by omega))

end CertificateChecks.KernelMisc.RuInv

end
