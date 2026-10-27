module

public import Certificates.Kernel.Sporadic.Fi22.FivePin
public import Certificates.Kernel.Sporadic.Fi22.C9554Sound
public import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Pin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W
open CertificateChecks.KernelSpor.Fi22C9554

section E8

variable (X Y H N1 N2 Z A B : Nat)

theorem e8_0 : e8 X Y H N1 N2 Z A B 0 = X := rfl
theorem e8_1 : e8 X Y H N1 N2 Z A B 1 = Y := rfl
theorem e8_2 : e8 X Y H N1 N2 Z A B 2 = H := rfl
theorem e8_3 : e8 X Y H N1 N2 Z A B 3 = N1 := rfl
theorem e8_4 : e8 X Y H N1 N2 Z A B 4 = N2 := rfl
theorem e8_5 : e8 X Y H N1 N2 Z A B 5 = Z := rfl
theorem e8_6 : e8 X Y H N1 N2 Z A B 6 = A := rfl
theorem e8_7 : e8 X Y H N1 N2 Z A B 7 = B := rfl

theorem e8_six {k : Nat} (hk : k < 6) : e8 X Y H N1 N2 Z A B k = six X Y H N1 N2 Z k := by
  have e : Nat.blt k 6 = true := by
    rw [Nat.blt_eq]
    exact hk
  unfold e8
  rw [e, cond_true]

end E8

noncomputable abbrev gA : Nat :=
  wd (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw))
    (fun k => Fi22X.inv (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2)
      (W zw) k)) g1w

noncomputable abbrev gB : Nat :=
  wd (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw))
    (fun k => Fi22X.inv (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2)
      (W zw) k)) g2w

theorem parts : pinK pin (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw)
    gA gB = true := by
  have h := ok
  unfold allPin at h
  simp only [Fi22C9554.strictB_eq] at h
  exact h

theorem parts' : allN 16 (fun k => Fi22X.cn (pin k)) = true ∧
    allN 8 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (pin k) (pin (k + 8))) = true ∧
    allN 8 (fun k => Nat.beq (pin k) (e8 (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1)
      (W nw2) (W zw) gA gB k)) = true ∧
    allN 8 (fun k => Nat.beq (pin (k + 8)) (Fi22X.inv (pin k))) = true := by
  have h := parts
  unfold pinK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem perm {k : Nat} (hk : k < 8) :
    permOK 3510 12 (mask 12) (3510 * 12) (pin k) (pin (k + 8)) = true :=
  allN_spec parts'.2.1 k hk

theorem inv_eq (k : Nat) (hk : k < 8) : pin (k + 8) = Fi22X.inv (pin k) :=
  Nat.eq_of_beq_eq_true (allN_spec parts'.2.2.2 k hk)

theorem pin_eq (k : Nat) (hk : k < 8) : pin k = e8 (W (signedWord wx)) (W (signedWord wy)) (W hw)
    (W nw1) (W nw2) (W zw) gA gB k :=
  Nat.eq_of_beq_eq_true (allN_spec parts'.2.2.1 k hk)

theorem x_eq : xA = unpack 3510 12 (pin 0) := by
  rw [pin_eq 0 (by norm_num), e8_0]
  exact Fi22FiveK.x_eq

theorem y_eq : yA = unpack 3510 12 (pin 1) := by
  rw [pin_eq 1 (by norm_num), e8_1]
  exact Fi22FiveK.y_eq

theorem h_eq : hA = unpack 3510 12 (pin 2) := by
  rw [pin_eq 2 (by norm_num), e8_2]
  exact Fi22FiveK.h_eq

theorem n1_eq : n1A = unpack 3510 12 (pin 3) := by
  rw [pin_eq 3 (by norm_num), e8_3]
  exact Fi22FiveK.n1_eq

theorem n2_eq : n2A = unpack 3510 12 (pin 4) := by
  rw [pin_eq 4 (by norm_num), e8_4]
  exact Fi22FiveK.n2_eq

theorem z_eq : zA = unpack 3510 12 (pin 5) := by
  rw [pin_eq 5 (by norm_num), e8_5]
  exact Fi22FiveK.z_eq

theorem perm6 : allN 6 (fun j => permOK 3510 12 (mask 12) (3510 * 12)
    (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw) j)
    (Fi22X.inv (six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw) j))) =
    true := by
  refine allN_intro fun j hj => ?_
  have e : six (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw) j = pin j := by
    rw [pin_eq j (by omega), e8_six _ _ _ _ _ _ _ _ hj]
  rw [e, ← inv_eq j (by omega)]
  exact perm (by omega)

theorem g1_eq : g1A = unpack 3510 12 (pin 6) := by
  rw [pin_eq 6 (by norm_num), e8_6]
  exact (g_eq perm6 Fi22FiveK.x_eq Fi22FiveK.y_eq Fi22FiveK.h_eq Fi22FiveK.n1_eq
    Fi22FiveK.n2_eq Fi22FiveK.z_eq).1

theorem g2_eq : g2A = unpack 3510 12 (pin 7) := by
  rw [pin_eq 7 (by norm_num), e8_7]
  exact (g_eq perm6 Fi22FiveK.x_eq Fi22FiveK.y_eq Fi22FiveK.h_eq Fi22FiveK.n1_eq
    Fi22FiveK.n2_eq Fi22FiveK.z_eq).2

end CertificateChecks.KernelSpor.Fi22Pin

end
