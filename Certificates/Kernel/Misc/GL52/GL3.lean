
module

public import Certificates.Kernel.Misc.GL52.LCLemmas
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG.Literature.GL52

theorem gl3Nodup : decide (gl3Elems.map keyGL3).Nodup = true := by
  quickRfl

theorem gl3Length : Nat.beq gl3Elems.length 168 = true := by
  quickRfl

theorem gl3Empty :
    (gl3Elems.all fun g => !(lkWord keyGL3 tblGL3 g).isEmpty || keyGL3 g == keyGL3 1) = true := by
  quickRfl

theorem gl3Cover : (gl3Elems.all fun g => hasKey tblGL3 (keyGL3 g)) = true := by
  quickRfl

theorem gl3Elems_ok : (gl3Elems.map keyGL3).Nodup ∧ gl3Elems.length = 168 := by
  have h₁ := of_decide_eq_true gl3Nodup
  have h₂ := Nat.eq_of_beq_eq_true gl3Length
  exact ⟨h₁, h₂⟩

theorem gl3_one (M : GL (Fin 3) (ZMod 2)) (h : lkWord keyGL3 tblGL3 M = []) : M = 1 := by
  have hm := mem_gl3Elems_of gl3Elems_ok M
  have h1 := mem_gl3Elems_of gl3Elems_ok 1
  have hM : (!(lkWord keyGL3 tblGL3 M).isEmpty || keyGL3 M == keyGL3 1) = true :=
    List.all_eq_true.1 gl3Empty M hm
  rw [h] at hM
  have hk : keyGL3 M = keyGL3 1 := by simpa using hM
  exact List.inj_on_of_nodup_map gl3Elems_ok.1 hm h1 hk

theorem keyGL3_mem (M : GL (Fin 3) (ZMod 2)) : ∃ e ∈ tblGL3, e.1 = keyGL3 M := by
  have h : hasKey tblGL3 (keyGL3 M) = true :=
    List.all_eq_true.1 gl3Cover M (mem_gl3Elems_of gl3Elems_ok M)
  exact mem_of_hasKey h

end CertificateChecks.KernelMisc.GL52L

end
