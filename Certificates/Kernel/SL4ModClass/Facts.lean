module

public import CFSG.Certificates.Kernel.SL4ModClassSound
public import Certificates.Kernel.SL4Mod.Facts
public import Certificates.Kernel.SL4ModClass.Chk0
public import Certificates.Kernel.SL4ModClass.Chk1
public import Certificates.Kernel.SL4ModClass.Chk2

public section

namespace CertificateChecks.KernelSL4ModClass

open CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

theorem lenK_all : ∀ n < 9, lenK n = true := by
  intro n hn
  interval_cases n
  exacts [lenK0, lenK1, lenK2, lenK3, lenK4, lenK5, lenK6, lenK7, lenK8]

theorem classK_all : ∀ n < 36, classK n = true := by
  intro n hn
  interval_cases n
  exacts [classK0, classK1, classK2, classK3, classK4, classK5, classK6, classK7, classK8,
    classK9, classK10, classK11, classK12, classK13, classK14, classK15, classK16, classK17,
    classK18, classK19, classK20, classK21, classK22, classK23, classK24, classK25, classK26,
    classK27, classK28, classK29, classK30, classK31, classK32, classK33, classK34, classK35]

theorem class_block {j i q : ℕ} (hj : j < 3) (hi : i < 3) (hq : q < 4) :
    checkClassFrom (tabL (KernelSL4Mod.cd j).tau) r14 r20 (KernelSL4Mod.od j i) (32 * q + 1)
      (((recs j i).drop (32 * q)).take 32) = true := by
  have h := classK_all (12 * j + 4 * i + q) (by omega)
  have e1 : (12 * j + 4 * i + q) / 12 = j := by omega
  have e2 : (12 * j + 4 * i + q) / 4 % 3 = i := by omega
  have e3 : (12 * j + 4 * i + q) % 4 = q := by omega
  rwa [classK, e1, e2, e3] at h

theorem recs_length {j i : ℕ} (hj : j < 3) (hi : i < 3) : (recs j i).length = 127 := by
  have hl := lenK_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rwa [lenK, e1, e2, beq_iff_eq] at hl

theorem checkClassFrom_ok {j i : ℕ} (hj : j < 3) (hi : i < 3) :
    checkClassFrom (tabL (KernelSL4Mod.cd j).tau) r14 r20 (KernelSL4Mod.od j i) 1 (recs j i) =
      true := by
  have hl := recs_length hj hi
  have b : ∀ q < 4, checkClassFrom (tabL (KernelSL4Mod.cd j).tau) r14 r20 (KernelSL4Mod.od j i)
      (32 * q + 1) (((recs j i).drop (32 * q)).take 32) = true := fun q hq => class_block hj hi hq
  have b3 := b 3 (by omega)
  rw [List.take_of_length_le (by rw [List.length_drop, hl]; omega)] at b3
  refine checkClassFrom_split 32 (by omega) (by simpa using b 0 (by omega)) ?_
  refine checkClassFrom_split 32 (by rw [List.length_drop, hl]; omega) (b 1 (by omega)) ?_
  rw [List.drop_drop]
  refine checkClassFrom_split 32 (by rw [List.length_drop, hl]; omega) (b 2 (by omega)) ?_
  rw [List.drop_drop]
  exact b3

theorem classCertData :
    ClassCertData 14 classRefRows14 ∧ ClassCertData 20 classRefRows20 := by
  refine classCertData_of fun j hj => ⟨KernelSL4Mod.cd j, KernelSL4Mod.tauK_all j hj,
    fun i hi => ⟨KernelSL4Mod.od j i, ?_, recs j i, recs_length hj hi, checkClassFrom_ok hj hi⟩⟩
  have h := KernelSL4Mod.orbK_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rwa [KernelSL4Mod.orbK, e1, e2] at h

end CertificateChecks.KernelSL4ModClass
