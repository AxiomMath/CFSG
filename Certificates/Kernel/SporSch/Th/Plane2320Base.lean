
module

public import Certificates.Kernel.SporSch.Th.Plane2320K
public import CFSG.Certificates.Kernel.SporSch.ThPlaneSound

@[expose] public section

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1)
open CertificateChecks.KernelSporSch.ThUA (all8 UB ltUB block_eq rowsA_eq un)
open CertificateChecks.KernelSporSch.ThKey (C1 C2)

theorem bBBall : ∀ i < 248, fBB i = true := by
  intro i hi
  have h8 : i / 31 < 8 := by omega
  have := allBlk_spec (BBs.all (i / 31) h8) (i % 31) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul 31 (i / 31)) (i % 31) = i := by
    rw [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod i 31
  rwa [e] at this

theorem bnd {x : Nat} (h : Nat.blt x (Nat.shiftLeft 1 248) = true) : x < 2 ^ 248 := by
  have := Nat.blt_eq.mp h
  rwa [sh1] at this

theorem rowsV_congr {f g : Nat → Nat} (h : ∀ i < 248, f i = g i) : rowsV f = rowsV g := by
  unfold CFSG.KS.SporSch.rowsV
  congr 1
  funext i
  rw [h i i.isLt]

theorem bB : ∀ i < 248, ThB i < 2 ^ 248 := fun i hi => bnd (allN_spec ltB i hi)
theorem bBB : ∀ i < 248, ThBB i < 2 ^ 248 := fun i hi => bnd (allN_spec ltBB i hi)
theorem bA : ∀ i < 248, ThA i < 2 ^ 248 := fun i hi => bnd (allN_spec ThUA.ltA i hi)

theorem rowsB_eq : CFSG.Sporadic.Th.Max3.rowsB = rowsV ThB := by
  rw [CFSG.Sporadic.Th.Max3.rowsB, ThSeedB.eq]
  exact thPay_sound seedB_ok

theorem bb_eq : mulRows CFSG.Sporadic.Th.Max3.rowsB CFSG.Sporadic.Th.Max3.rowsB = rowsV ThBB := by
  rw [rowsB_eq]
  exact mulRows_sound bB bB (un (fun _ => rfl) bBBall)

theorem len_w : (invWord transporterWord).length = 35 := by decide

theorem letters (k : Nat) (hk : k < 35) :
    ((invWord transporterWord).map abLetterRows)[k]! = rowsV (letRow ThVI.LC ThA ThBB k) := by
  have hl : k < (invWord transporterWord).length := by rw [len_w]; exact hk
  rw [getElem!_pos _ k (by simpa using hl), List.getElem_map, ← getElem!_pos _ k hl]
  rcases wc_sound wc k hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    have e : letRow ThVI.LC ThA ThBB k = ThA := by
      funext i
      unfold letRow
      rw [h2]
      rfl
    rw [e, ← rowsA_eq]
    simp [abLetterRows]
  · rw [h1]
    have e : letRow ThVI.LC ThA ThBB k = ThBB := by
      funext i
      unfold letRow
      rw [h2]
      rfl
    rw [e, ← bb_eq]
    simp [abLetterRows]

end CertificateChecks.KernelSporSch.ThPlane

end
