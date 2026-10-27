module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntData

public section

namespace CertificateChecks.KernelMisc.HS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native CFSG.KC.Misc.HexFlat

theorem hs100Arr_eq (j : ℕ) (hj : j < 16) : hs100Arr j = unpack 100 7 (HX.F j) := by
  rw [hs100Arr, HX.eq]
  exact hexTable3_sound HX.all j hj

theorem c_binds : Binds 100 7 C.S 15 5 C.BP hs100StrongArrs hs100BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100StrongArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← Nat.eq_of_beq_eq_true (allN_spec cFS j hj), ← hs100Arr_eq j (by omega)]
  unfold hs100StrongArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem s5InP_unpack {G : ℕ} (h : CFSG.KC.PermWit.siftR 100 7 C.LR C.TRI C.BP 5 G = true) :
    CFSG.EvenSporadicStandard.HSStd.s5InP (unpack 100 7 G) = true := by
  unfold CFSG.EvenSporadicStandard.HSStd.s5InP CFSG.EvenSporadicStandard.HSStd.s5Levels
  exact CFSG.KC.PermWit.siftR_sound c_binds cperm C.hl h

theorem sz : szOK 100 7 = true := by decide +kernel

end CertificateChecks.KernelMisc.HS100

end
