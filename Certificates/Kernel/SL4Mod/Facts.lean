module

public import CFSG.Certificates.Kernel.SL4ModSound
public import Certificates.Kernel.SL4Mod.Tau
public import Certificates.Kernel.SL4Mod.Spin0
public import Certificates.Kernel.SL4Mod.Spin1
public import Certificates.Kernel.SL4Mod.Spin2

public section

namespace CertificateChecks.KernelSL4Mod

open CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

theorem tauK_all : ∀ j < 3, tauK j = true := by
  intro j hj
  interval_cases j
  exacts [tauK0, tauK1, tauK2]

theorem orbK_all : ∀ n < 9, orbK n = true := by
  intro n hn
  interval_cases n
  exacts [orbK0, orbK1, orbK2, orbK3, orbK4, orbK5, orbK6, orbK7, orbK8]

theorem lenK_all : ∀ n < 9, lenK n = true := by
  intro n hn
  interval_cases n
  exacts [lenK0, lenK1, lenK2, lenK3, lenK4, lenK5, lenK6, lenK7, lenK8]

theorem spinK_all : ∀ n < 36, spinK n = true := by
  intro n hn
  interval_cases n
  exacts [spinK0, spinK1, spinK2, spinK3, spinK4, spinK5, spinK6, spinK7, spinK8, spinK9,
    spinK10, spinK11, spinK12, spinK13, spinK14, spinK15, spinK16, spinK17, spinK18, spinK19,
    spinK20, spinK21, spinK22, spinK23, spinK24, spinK25, spinK26, spinK27, spinK28, spinK29,
    spinK30, spinK31, spinK32, spinK33, spinK34, spinK35]

theorem spin_block {j i q : ℕ} (hj : j < 3) (hi : i < 3) (hq : q < 4) :
    checkSpinFrom (tabL (cd j).tau) (od j i) (32 * q + 1) (((certs j i).drop (32 * q)).take 32) =
      true := by
  have h := spinK_all (12 * j + 4 * i + q) (by omega)
  have e1 : (12 * j + 4 * i + q) / 12 = j := by omega
  have e2 : (12 * j + 4 * i + q) / 4 % 3 = i := by omega
  have e3 : (12 * j + 4 * i + q) % 4 = q := by omega
  rwa [spinK, e1, e2, e3] at h

theorem checkSpinL_ok {j i : ℕ} (hj : j < 3) (hi : i < 3) :
    checkSpinL (cd j) (od j i) (certs j i) = true := by
  have hl := lenK_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rw [lenK, e1, e2, beq_iff_eq] at hl
  rw [checkSpinL, hl, beq_self_eq_true, Bool.true_and]
  have b : ∀ q < 4, checkSpinFrom (tabL (cd j).tau) (od j i) (32 * q + 1)
      (((certs j i).drop (32 * q)).take 32) = true := fun q hq => spin_block hj hi hq
  have b3 := b 3 (by omega)
  rw [List.take_of_length_le (by rw [List.length_drop, hl]; omega)] at b3
  refine checkSpinFrom_split 32 (by omega) (by simpa using b 0 (by omega)) ?_
  refine checkSpinFrom_split 32 (by rw [List.length_drop, hl]; omega) (b 1 (by omega)) ?_
  rw [List.drop_drop]
  refine checkSpinFrom_split 32 (by rw [List.length_drop, hl]; omega) (b 2 (by omega)) ?_
  rw [List.drop_drop]
  exact b3

theorem spinCertData : SpinCertData := by
  refine spinCertData_of fun j hj => ⟨cd j, tauK_all j hj, fun i hi => ⟨od j i, ?_, certs j i,
    checkSpinL_ok hj hi⟩⟩
  have h := orbK_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rwa [orbK, e1, e2] at h

end CertificateChecks.KernelSL4Mod
