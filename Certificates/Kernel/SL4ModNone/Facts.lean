module

public import CFSG.Certificates.Kernel.SL4ModNoneSound
public import Certificates.Kernel.SL4Mod.Facts
public import Certificates.Kernel.SL4ModNone.Chk0
public import Certificates.Kernel.SL4ModNone.Chk1
public import Certificates.Kernel.SL4ModNone.Chk2

public section

namespace CertificateChecks.KernelSL4ModNone

open CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

theorem len_all : ∀ n < 9, ch705102len n = true := by
  intro n hn
  interval_cases n
  exacts [ch705102len0, ch705102len1, ch705102len2, ch705102len3, ch705102len4, ch705102len5,
    ch705102len6, ch705102len7, ch705102len8]

theorem blk_all : ∀ n < 36, ch705102blk n = true := by
  intro n hn
  interval_cases n
  exacts [ch705102blk0, ch705102blk1, ch705102blk2, ch705102blk3, ch705102blk4, ch705102blk5,
    ch705102blk6, ch705102blk7, ch705102blk8, ch705102blk9, ch705102blk10, ch705102blk11,
    ch705102blk12, ch705102blk13, ch705102blk14, ch705102blk15, ch705102blk16, ch705102blk17,
    ch705102blk18, ch705102blk19, ch705102blk20, ch705102blk21, ch705102blk22, ch705102blk23,
    ch705102blk24, ch705102blk25, ch705102blk26, ch705102blk27, ch705102blk28, ch705102blk29,
    ch705102blk30, ch705102blk31, ch705102blk32, ch705102blk33, ch705102blk34, ch705102blk35]

theorem none_block {j i q : ℕ} (hj : j < 3) (hi : i < 3) (hq : q < 4) :
    checkNoneFrom (tabL (KernelSL4Mod.cd j).tau) (KernelSL4Mod.od j i) (16 * q)
      (((ents j i).drop (16 * q)).take 16) = true := by
  have h := blk_all (12 * j + 4 * i + q) (by omega)
  have e1 : (12 * j + 4 * i + q) / 12 = j := by omega
  have e2 : (12 * j + 4 * i + q) / 4 % 3 = i := by omega
  have e3 : (12 * j + 4 * i + q) % 4 = q := by omega
  rwa [ch705102blk, e1, e2, e3] at h

theorem ents_length {j i : ℕ} (hj : j < 3) (hi : i < 3) : (ents j i).length = 64 := by
  have hl := len_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rwa [ch705102len, e1, e2, beq_iff_eq] at hl

theorem checkNoneFrom_ok {j i : ℕ} (hj : j < 3) (hi : i < 3) :
    checkNoneFrom (tabL (KernelSL4Mod.cd j).tau) (KernelSL4Mod.od j i) 0 (ents j i) = true := by
  have hl := ents_length hj hi
  have b : ∀ q < 4, checkNoneFrom (tabL (KernelSL4Mod.cd j).tau) (KernelSL4Mod.od j i) (16 * q)
      (((ents j i).drop (16 * q)).take 16) = true := fun q hq => none_block hj hi hq
  have b3 := b 3 (by omega)
  rw [List.take_of_length_le (by rw [List.length_drop, hl])] at b3
  refine checkNoneFrom_split 16 (by omega) (by simpa using b 0 (by omega)) ?_
  refine checkNoneFrom_split 16 (by rw [List.length_drop, hl]; omega) (b 1 (by omega)) ?_
  rw [List.drop_drop]
  refine checkNoneFrom_split 16 (by rw [List.length_drop, hl]; omega) (b 2 (by omega)) ?_
  rw [List.drop_drop]
  exact b3

theorem noneCertData : NoneCertData := by
  intro j hj
  refine ⟨KernelSL4Mod.cd j, KernelSL4Mod.tauK_all j hj,
    fun i hi => ⟨KernelSL4Mod.od j i, ?_, ents j i, ents_length hj hi, checkNoneFrom_ok hj hi⟩⟩
  have h := KernelSL4Mod.orbK_all (3 * j + i) (by omega)
  have e1 : (3 * j + i) / 3 = j := by omega
  have e2 : (3 * j + i) % 3 = i := by omega
  rwa [KernelSL4Mod.orbK, e1, e2] at h

end CertificateChecks.KernelSL4ModNone
