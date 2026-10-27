module

public import Certificates.Kernel.HeLoc.MemDefs
public import Certificates.Kernel.HeLoc.FiveFacts

public section

namespace CertificateChecks.KernelHeLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CFSG.KC.Misc.Clos (forall_of_chunks)

theorem memAt_all {G F f : Nat} (h : ∀ c < 10, memB G F f c = true) :
    ∀ x < 8330, memAt G F f x = true := by
  have h' := forall_of_chunks 833 10 (memAt G F f) h
  exact fun x hx => h' x (by omega)

theorem mem_of_memB
    {G GI F f : Nat} (hp : permOK 8330 14 (mask 14) (8330 * 14) G GI = true)
    (hF : nfValidK 5 HeC.LR F = true) (hf : f < 2) (h : ∀ c < 10, memB G F f c = true) :
    Rep 8330 (unpack 8330 14 G) (permOfArr 8330 (unpack 8330 14 G)) ∧
      permOfArr 8330 (unpack 8330 14 G) ∈ heAutGroup ∧
      (permOfArr 8330 (unpack 8330 14 G) ∈ heP ↔ f = 0) := by
  have hR : Rep 8330 (unpack 8330 14 G) (permOfArr 8330 (unpack 8330 14 G)) :=
    (rep_permOfArr (invEqK_sound (n := 8330) (w := 14) (p := G) (r := GI) hp).2).1
  have hRF := Five.repF_of_rep hR
  have hall := memAt_all h
  refine ⟨hR, ?_⟩
  set g := permOfArr 8330 (unpack 8330 14 G)
  rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl
  · have he : g = Five.El F := hRF.unique fun x hx => by
      have h1 := hall x hx
      unfold memAt at h1
      rw [CFSG.KS.SporSch.blt_true hx] at h1
      exact (Nat.eq_of_beq_eq_true h1).trans (Five.El_rep hF x hx)
    have hm := Five.El_mem hF
    rw [← he] at hm
    exact ⟨heP_le_heAutGroup hm, iff_of_true hm rfl⟩
  · have he : g * heAutU = Five.El F := (hRF.comp Five.hU).unique fun x hx => by
      have h1 := hall x hx
      unfold memAt at h1
      rw [CFSG.KS.SporSch.blt_true hx] at h1
      exact (Nat.eq_of_beq_eq_true h1).trans (Five.El_rep hF x hx)
    have hm := Five.El_mem hF
    have e : g = Five.El F * heAutU⁻¹ := by rw [← he, mul_inv_cancel_right]
    refine ⟨?_, iff_of_false (fun hg => heAutU_not_mem ?_) (by decide)⟩
    · rw [e]
      exact heAutGroup.mul_mem (heP_le_heAutGroup hm) (heAutGroup.inv_mem heAutU_mem_heAutGroup)
    · have e2 : heAutU = g⁻¹ * Five.El F := by rw [← he, inv_mul_cancel_left]
      rw [e2]
      exact heP.mul_mem (heP.inv_mem hg) hm

end CertificateChecks.KernelHeLoc

end
