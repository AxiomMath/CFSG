module

public import Certificates.Kernel.MonsterB.Co2Vecs
public import CFSG.Certificates.Kernel.MonsterB.Co2MemSound

public section

namespace CertificateChecks.KernelMonB

open CFSG.KS.Raw CFSG.KC.Enum CFSG.KC.Co2Mem

@[expose] noncomputable def vecF (t : Nat) : Nat := pg 24 (CFSG.KS.mask 24) (Co2V.F 0) t

theorem vectors_getElem! {t : Nat} (ht : t < 2300) :
    (CFSG.Monster.B.Co2.Native.vectors ())[t]! = vecF t := by
  rw [vectors_eq, unpack, getElem!_pos _ _ (by simpa using ht), Array.getElem_ofFn]
  rfl

theorem vectors_contains_eq (y : Nat) :
    (CFSG.Monster.B.Co2.Native.vectors ()).contains y = memK 2300 24 (Co2V.F 0) y := by
  rw [Bool.eq_iff_iff, memK_iff, vectors_eq, Array.contains_iff_mem, unpack, Array.mem_ofFn]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.1, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

theorem vectors_all_iff (p : Nat → Bool) :
    (CFSG.Monster.B.Co2.Native.vectors ()).all p = true ↔ ∀ t < 2300, p (vecF t) = true := by
  rw [vectors_eq, Array.all_eq_true]
  constructor
  · intro h t ht
    have := h t (by simpa [unpack] using ht)
    simpa [unpack, vecF] using this
  · intro h t ht
    have ht' : t < 2300 := by simpa [unpack] using ht
    simpa [unpack, vecF] using h t ht'

end CertificateChecks.KernelMonB

end
