module

public import Certificates.Kernel.Misc.Perm.J2CentB0
public import Certificates.Kernel.Misc.Perm.J2CentB1
public import Certificates.Kernel.Misc.Perm.J2CentB2
public import Certificates.Kernel.Misc.Perm.J2CentB3
public import CFSG.Certificates.Kernel.J2CentSound
public import CFSG.Certificates.Kernel.J2Enum.Group
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J2CoverSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.J2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Enum CFSG.KC.J2Cent CFSG.KC.Child3
open CertificateChecks.KernelJ2Cover CFSG.ComponentClassification.J2Cover
open CertificateChecks.KernelMisc.J2C3 (X)
open CertificateChecks.KernelMisc.J2Fam (V1)

theorem sumF_congr {f g : Nat → Nat} : ∀ m, (∀ a < m, f a = g a) → sumF m f = sumF m g
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ r : Nat → Nat, sumF (m + 1) r = sumF m r + r m := fun r => by
      change strictN (sumF m r) (fun s' => Nat.add s' (r m)) = _
      cases sumF m r <;> rfl
    rw [e, e, sumF_congr m fun a ha => h a (by omega), h m (by omega)]

theorem allC : ∀ a < 315, fC a = true := by
  intro a ha
  have c0 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) B0.all
  have c1 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) B1.all
  have c2 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) B2.all
  have c3 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) B3.all
  simp only [fC0, fC1, fC2, fC3, Nat.add_eq] at c0 c1 c2 c3
  rcases Nat.lt_or_ge a 80 with h0 | h0
  · exact c0 a h0
  rcases Nat.lt_or_ge a 160 with h1 | h1
  · have := c1 (a - 80) (by omega)
    rwa [Nat.add_sub_cancel' h0] at this
  rcases Nat.lt_or_ge a 240 with h2 | h2
  · have := c2 (a - 160) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · have := c3 (a - 240) (by omega)
    rwa [Nat.add_sub_cancel' h2] at this

theorem kL0 : rcnt (PA.LR 0) = 315 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem k20 : rcnt (PA.LR 0) * rcnt (PA.LR 1) * rcnt (PA.LR 2) < 2 ^ 20 := by
  have h1 : Nat.beq (rcnt (PA.LR 1)) 160 = true := by quickRfl
  have h2 : Nat.beq (rcnt (PA.LR 2)) 12 = true := by quickRfl
  rw [kL0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  norm_num

theorem sumC : sumF (rcnt (PA.LR 0)) (blkCent 315 9 PA.LR PA.TR PA.BP X V1) =
    sumF 315 (fun a => lget CT (blkKey 315 9 PA.LR PA.TR PA.BP a)) := by
  rw [kL0]
  exact sumF_congr 315 fun a ha => Nat.eq_of_beq_eq_true (allC a ha)

theorem kx : Nat.beq (fld20 (sumF 315 (fun a => lget CT (blkKey 315 9 PA.LR PA.TR PA.BP a))) 0)
    36 = true := by quickRfl

theorem kv : Nat.beq (fld20 (sumF 315 (fun a => lget CT (blkKey 315 9 PA.LR PA.TR PA.BP a))) 1)
    240 = true := by quickRfl

theorem chainPA : ChainOK3 315 9 7 2 PA.BP 20 16 PA.S PA.SI PA.LR PA.TR PA.TRI autD autStrong
    autBase :=
  ⟨binds, PA.head, PA.hl, by norm_num, PA.hs, perm⟩

theorem memX : ∃ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 X ξ :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 X (by quickRfl)).1 (by quickRfl)

theorem memV1 : ∃ ν ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 V1 ν :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 V1 (by quickRfl)).1 (by quickRfl)

theorem card_cent_x {ξ : Equiv.Perm (Fin 315)} (hξ : ξ ∈ Raw.Orb.Gen 315 autStrong 2)
    (hX : Raw.Orb.PRep 315 9 X ξ) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ξ = ξ * g} =
      36 := by
  obtain ⟨ν, hν, hV⟩ := memV1
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).1, sumC, Nat.eq_of_beq_eq_true kx]

theorem card_cent_v1 {ν : Equiv.Perm (Fin 315)} (hν : ν ∈ Raw.Orb.Gen 315 autStrong 2)
    (hV : Raw.Orb.PRep 315 9 V1 ν) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ν = ν * g} =
      240 := by
  obtain ⟨ξ, hξ, hX⟩ := memX
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).2, sumC, Nat.eq_of_beq_eq_true kv]

end CertificateChecks.KernelMisc.J2Cent

end
