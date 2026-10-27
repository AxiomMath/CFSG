
module

public import Certificates.Kernel.SporSch.Co2M.FratS0
public import Certificates.Kernel.SporSch.Co2M.FratS1
public import Certificates.Kernel.SporSch.Co2M.FratS2
public import Certificates.Kernel.SporSch.Co2M.FratS3
public import Certificates.Kernel.SporSch.Co2M.FratS4
public import Certificates.Kernel.SporSch.Co2M.FratYB
public import Certificates.Kernel.SporSch.Co2M.FratM
public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2LF

namespace CertificateChecks.KernelSporSch.Co2LF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.Sporadic.Co2Schreier
open CertificateChecks.KernelSporSch.Co2M CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem baseOK : (Nat.beq fratBase.size 2 &&
    allN 2 fun t => Nat.beq fratBase[t]! (pg 12 (mask 12) BP t)) = true := by
  quickRfl

theorem perm : allN 16 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem S_eq {k : ℕ} (hk : k < 16) : fratStrong[k]! = unpack 2300 12 (S k) :=
  (unpack_eq (repT_get fratRep (by rw [fratT_len]; exact hk)) (allN_spec sb k hk)).symm

theorem binds : Binds 2300 12 S 16 2 BP fratStrong fratBase := by
  have hb := baseOK
  rw [Bool.and_eq_true] at hb
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => S_eq hj,
    Nat.eq_of_beq_eq_true hb.1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩
  rw [fratRep.1, fratT_len]

theorem orig_eq : fratOrig = fratStrong.extract 0 12 := by
  apply Array.ext
  · simp [fratStrong, extendArrs_size, fratOrigRep.1, fratT0_len]
  · intro i h1 h2
    have hi : i < fratOrig.size := h1
    rw [Array.getElem_extract, ← getElem!_pos fratStrong _ (by simp at h2; omega),
      ← getElem!_pos fratOrig i h1]
    simp only [Nat.zero_add]
    exact (extendArrs_get_lt fratOrig fratDerivs hi).symm

theorem words_eq : fratWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 12 16 fratDerivs :=
  wordsArr_eq (by decide +kernel) (by norm_num) (fun j hj => by
    simp only [fratWords]
    rw [getElem!_pos _ j (by simp; omega)]
    simp only [List.getElem_toArray]
    interval_cases j <;> rfl)
    (by decide +kernel)

theorem chain_ok : rawChainOK 2300 fratOrig fratStrong fratBase fratWords 4 = true := by
  rw [orig_eq, words_eq]
  exact rawChainK_sound binds head hl (by norm_num) hs

theorem orbits_ok : rawOrbitSizes 2300 fratStrong fratBase = [128, 64] := by
  rw [rawOrbitSizesK_sound binds perm hl]
  decide +kernel

end CertificateChecks.KernelSporSch.Co2LF

end
