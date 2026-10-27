
module


public import Certificates.Kernel.J4Count.KFacts
public import CFSG.Certificates.Kernel.J4FixCSoundPrelude

public section

namespace CertificateChecks.KernelJ4Count.FixCPair

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.KS.SporSch.C11 CFSG.KC.J4FixC
open CFSG.Sporadic.SmallF2.Native

theorem peqK_of_eq {g : J} {p q : ℕ} (hp : PairRep g p)
    (hq : PairRep g q) : peqK p q = true := by
  obtain ⟨k, hk, e, hkC⟩ := hp
  obtain ⟨k', hk', e', hkD⟩ := hq
  have hn : k' * k⁻¹ ∈ K ⊓ N := by
    refine ⟨K.mul_mem hk' (K.inv_mem hk), ?_⟩
    have : k' * k⁻¹ = η (paK q) * η (paK p) := by
      calc k' * k⁻¹ = (η (paK q))⁻¹ * (η (paK q) * k') * k⁻¹ := by group
        _ = (η (paK q))⁻¹ * (η (paK p) * k) * k⁻¹ := by rw [← e', e]
        _ = η (paK q) * η (paK p) := by rw [η_inv_self]; group
    rw [this]
    exact N.mul_mem (η_mem_N _) (η_mem_N _)
  rw [K_inf_N, Subgroup.mem_bot] at hn
  have hkk : k' = k := by
    calc k' = k' * k⁻¹ * k := by group
      _ = k := by rw [hn, one_mul]
  subst hkk
  have ha : paK p = paK q := by
    have : η (paK p) = η (paK q) := mul_right_cancel (e.symm.trans e')
    exact η_injOn (paK_lt p) (paK_lt q) this
  refine peqK_of ha ?_
  have hb : ∀ b, app11 (unpack11 (pcK p)) b = app11 (unpack11 (pcK q)) b := fun b =>
    η_injOn (vecMulN_lt (cols_bdd _) b) (vecMulN_lt (cols_bdd _) b) ((hkC b).symm.trans (hkD b))
  have hs1 := (unpack11_bounded (pcK p)).1
  have hs2 := (unpack11_bounded (pcK q)).1
  refine Array.ext (by rw [hs1, hs2]) fun j h1 h2 => ?_
  have hj : j < 11 := by rwa [hs1] at h1
  have c1 := app11_two_pow (cols_bdd (pcK p)) hj
  have c2 := app11_two_pow (cols_bdd (pcK q)) hj
  rw [hb, c2, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at c1
  simpa using c1.symm

theorem pairRep_eq {g h : J} {p q : ℕ}
    (hg : PairRep g p) (hh : PairRep h q) (e : peqK p q = true) : g = h := by
  obtain ⟨e1, e2⟩ := peqK_spec e
  obtain ⟨k, hk, rfl, hkC⟩ := hg
  obtain ⟨k', hk', rfl, hkD⟩ := hh
  rw [e2] at hkC
  rw [e1, CertificateChecks.KernelJ4Count.eq_of_actsBy' hk hk' hkC hkD]

end CertificateChecks.KernelJ4Count.FixCPair

end
