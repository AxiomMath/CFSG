module

public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.HData
public import CFSG.LargeExtraspecial.S63CD4Inputs
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CertificateChecks.KernelS63.ID

open CFSG.LargeExtraspecial.S63 CFSG.KC.Co1F2

theorem gens_size : d4Gens.size = 8 := by decide +kernel

theorem gens_chk : ((List.range 8).all fun k => d4Gens[k]! == unpackR 24 (G k)) = true := by
  decide +kernel

theorem gens_eq : ∀ k < 8, d4Gens[k]! = unpackR 24 (G k) := fun k hk => by
  have h := List.all_eq_true.1 gens_chk k (List.mem_range.2 hk)
  simpa using h

theorem ug_chk : ((List.range 4).all fun l =>
    Nat.beq (CertificateChecks.KernelS63.HD.UG l) (G (uIdx.getD l 0))) = true := by
  decide +kernel

theorem ug_eq : ∀ l < 4, CertificateChecks.KernelS63.HD.UG l = G (uIdx.getD l 0) := fun l hl => by
  have h := List.all_eq_true.1 ug_chk l (List.mem_range.2 hl)
  exact Nat.eq_of_beq_eq_true h

end CertificateChecks.KernelS63.ID

end
