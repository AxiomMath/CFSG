module

public import Certificates.Kernel.SporSch.Co2S.ItStab
public import CFSG.Certificates.Kernel.SporSch.KeySearchOrbit
public import CFSG.Sporadic.Co2Schreier.OrbitCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2It

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix
open CFSG.KS.SporSch.KeySearch
open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem permA_of_rep {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    PermA n t := by
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_⟩
  · rw [h ⟨x, hx⟩]
    exact (g ⟨x, hx⟩).isLt
  · rw [h ⟨x, hx⟩, h ⟨y, hy⟩] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

theorem aArrs_size : aArrs.size = 2 := by
  rw [aArrs, Co2Order.orig_eq, Array.size_extract, Co2A.binds.2.2.2.1]
  rfl

theorem aArrs_get (k : Nat) (hk : k < 2) : aArrs[k]! = unpack 2300 12 (Co2ItC.S k) := by
  rw [aArrs, Co2Order.a_eq k hk, Nat.eq_of_beq_eq_true (allN_spec gens k hk)]

theorem perm_hd (k : Nat) (hk : k < 2) :
    permOK 2300 12 (mask 12) (2300 * 12) (Co2ItC.S k) (Co2ItC.SI k) = true := by
  have h : headJ 2300 12 (mask 12) (2300 * 12) (CFSG.KC.Enum.pidn 2300 12) Co2ItC.S Co2ItC.SI 2
      Co2ItC.D 9 Co2ItC.BP k = true := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact Co2ItC.hd0
    · exact Co2ItC.hd1
  exact ((bAnd_iff _ _).1 h).1

theorem aArrs_perm : ∀ k < aArrs.size, PermA 2300 aArrs[k]! := fun k hk => by
  rw [aArrs_size] at hk
  rw [aArrs_get k hk]
  exact permA_of_rep (Co2Order.rep_unpack (perm_hd k hk)).1

theorem closure_aArrs : co2P = Subgroup.closure (Set.range fun j : Fin aArrs.size =>
    permOfArr 2300 aArrs[j.val]!) := by
  have e : (Set.range fun j : Fin aArrs.size => permOfArr 2300 aArrs[j.val]!) =
      {co2Gen 0, co2Gen 1} := by
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j.val < 2 := aArrs_size ▸ j.isLt
      rcases (by omega : j.val = 0 ∨ j.val = 1) with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by rw [aArrs_size]; norm_num⟩, rfl⟩
      · exact ⟨⟨1, by rw [aArrs_size]; norm_num⟩, rfl⟩
  rw [e]
  rfl

theorem it_good : Good 2300 co2ItNat := by
  unfold Good
  decide +kernel

theorem record :
    orbitRecordOK co2ItNat 1024650 (co3KeySearch aArrs co2ItNat 1024650) = true := by
  obtain ⟨h1, h2, h3⟩ := keySearch_spec (n := 2300) (bound := 1024650) (by norm_num) aArrs_perm
    it_good
  have hsz := h3 fun F h0 hF =>
    orbit_card.trans (orbit_le_card closure_aArrs aArrs_perm it_good F h0 hF)
  unfold orbitRecordOK
  rw [h1, h2, hsz]
  rfl

end CertificateChecks.KernelSporSch.Co2It

end
