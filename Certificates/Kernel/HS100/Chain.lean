module

public import Certificates.Kernel.HS100.ChainData
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat CFSG.RankThree.Native
open CFSG.Monster.B.Co2.Native

theorem hs100Arr_eq (j : ℕ) (hj : j < 16) : hs100Arr j = unpack 100 7 (HP.F j) := by
  rw [hs100Arr, HP.eq]
  exact hexTable3_sound HP.all j hj

theorem binds : Binds 100 7 HC.S 15 5 HC.BP hs100StrongArrs hs100BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100StrongArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← Nat.eq_of_beq_eq_true (allN_spec HC.FS j hj), ← hs100Arr_eq j (by omega)]
  unfold hs100StrongArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem siftP {g : Array ℕ} {G : ℕ} (hg : g = unpack 100 7 G)
    (h : (Nat.beq (Nat.shiftRight G (100 * 7)) 0 && allN 100 (fun t => Nat.blt (pg 7 (mask 7) G t) 100)
      && siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 G) = true) :
    siftA 100 hs100PLevels hs100BaseArr 0 g = true := by
  simp only [Bool.and_eq_true] at h
  exact siftK_soundR binds HC.perm HC.hl hg (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

end CertificateChecks.KernelHS100

end
