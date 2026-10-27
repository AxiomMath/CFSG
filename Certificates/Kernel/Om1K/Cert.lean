module

public import Certificates.Kernel.Om1K.GlueB
public import Certificates.Kernel.Om1K.GlueO

public section

namespace CertificateChecks.KernelOm1

open Certificates in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Facts in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt) in
theorem cert :
    (E wT0 = t ∧ E wI0 * E wI0 = t ∧ E wJ0 * E wJ0 = t ∧ E wJ0 * E wI0 * (E wJ0)⁻¹ = (E wI0)⁻¹ ∧
      E wG1 * t * (E wG1)⁻¹ = t * z ∧ (∀ w ∈ wT ++ [wS1], Commute (E w) t) ∧
      (∀ w ∈ wCa, Commute (E w) ta) ∧ (∀ w ∈ wCc, Commute (E w) tc) ∧ tb = z * ta) ∧
    (Nat.card (G wS0) = 4096 ∧ Nat.card (G wP3) = 27 ∧ Nat.card (G wSa) = 2048 ∧
      Nat.card (G wPa3) = 9 ∧ Nat.card (G wPa5) = 5 ∧ Nat.card (G wSc) = 1024 ∧
      Nat.card (G wPc) = 3) ∧
    (3150 ≤ (orb (G wX) (neg 15)).ncard ∧ 3780 ≤ (orb (G wX) (neg 3)).ncard ∧
      113400 ≤ (orb (G wX) (neg 23)).ncard) ∧
    (∀ g ∈ G wX, g '' neg 15 = neg 15 ∨ g '' neg 15 = E wG1 '' neg 15 ∨
      ∃ w ∈ wSub, ∃ s ∈ G wT, g '' neg 15 = (s * E w) '' neg 15) ∧
    (∀ w ∈ wSub, 3150 ≤ (orb (G (wT ++ [w])) (neg 15)).ncard) ∧
    (∀ d ∈ maskData, d.2.1 < 4 ∧ E d.2.2 * e d.1 * (E d.2.2)⁻¹ = e (repMasks.getD d.2.1 0)) ∧
    (∀ x ∈ G wS0, ∀ y ∈ G wS0, x * x = t → y * y = t → y * x * y⁻¹ = x⁻¹ →
      (x ∈ R ∧ y ∈ R) ∨ (x ∈ R' ∧ y ∈ R') ∨ ∃ s ∈ G wT, TwinFail x y s) ∧
    ((∀ x ∈ G wSa, x * x ≠ tb) ∧ ∀ x ∈ G wSa, ∀ y ∈ G wSa, x * x = ta → y * y = ta →
      y * x * y⁻¹ ≠ x⁻¹) ∧
    (∀ x ∈ G wSc, ∀ y ∈ G wSc, x * x = tc → y * y = tc → y * x * y⁻¹ = x⁻¹ →
      ∃ s ∈ G wCc, TwinFail x y s) ∧
    576 ≤ {p | ∃ s ∈ G wT, p = tup s}.ncard ∧
    ({x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) (↑R ∪ ↑R') D x}.ncard ≤ 64 ∧
      {x | x ∈ G wP3 ∧ ¬ OmGen.BadElt (G wT) (↑R ∪ ↑R') D x}.ncard ≤ 3) ∧
    Nat.card R ≤ 8 :=
  ⟨rel_fact, enum_fact, orbit_fact, cover_fact, trans_fact, mask_fact, q80_fact, q8a_fact,
    q8c_fact, tuple_fact, bad_fact, r0_fact⟩

end CertificateChecks.KernelOm1

end
