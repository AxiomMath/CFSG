
module

public import Certificates.Kernel.Sporadic.ON3.Words
public import Certificates.Kernel.Sporadic.ON3.Tab0
public import Certificates.Kernel.Sporadic.ON3.Tab1
public import Certificates.Kernel.Sporadic.ON3.Tab2
public import Certificates.Kernel.Sporadic.ON3.Tab3
public import Certificates.Kernel.Sporadic.ON3.Tab4
public import Certificates.Kernel.Sporadic.ON3.Tab5
public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public import Certificates.Kernel.Sporadic.ON.Seven

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON3.tabAll CertificateChecks.KernelSpor.ON3.tabS 120

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS

theorem tab_at {x : Nat} (hx : x < 245520) : tabAt x = true := by
  have hs : x / 2046 < 120 := by omega
  have h := allN_spec (tabAll (x / 2046) hs) (x % 2046) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 2046) 2046) (x % 2046) = x := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem strictB_eq'' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem tab_facts {x : Nat} (hx : x < 245520) :
    ZT x = trW 0 x ∧ QT x = trW 1 x ∧ CT x = trW 2 x ∧ CIT (CT x) = x ∧ D1T x = trW 3 x ∧
    D2T x = trW 4 x ∧ D3T x = trW 5 x ∧ D4T x = trW 6 x ∧ M2T x = trW 7 x ∧ M3T x = trW 8 x ∧
    L1T x = trW 9 x ∧ L2T x = trW 10 x ∧ WT x = CT (QT (QT (CIT x))) ∧ ZT (ZT x) = x ∧
    M2T (ZT x) = ZT (M2T x) ∧ M3T (ZT x) = ZT (M3T x) ∧ QT (QT (QT (QT x))) = x ∧
    L1T (QT x) = QT (L1T x) ∧ L2T (QT x) = QT (L2T x) ∧ D1T x = CT (ZT (CIT x)) ∧
    ∀ j < 4, WT (DT j x) = DT j (WT x) := by
  have h := tab_at hx
  unfold tabAt at h
  simp only [strictB_eq'', bAnd_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun j hj => by simpa only [Nat.beq_eq] using allN_spec h21 j hj⟩

end CertificateChecks.KernelSpor.ON3

end
