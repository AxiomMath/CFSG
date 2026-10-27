module

public import Certificates.Kernel.SporSch.Ly.FiveTbData
public import CFSG.Certificates.Kernel.SporSch.LyFiveTbSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

namespace CertificateChecks.KernelSporSch.LyFT

open CFSG.KC.LyFiveTb CFSG.KS.LyFiveTb CFSG.RankThree.Native

theorem par_eq : lyFiveParArr = CFSG.KS.Raw.unpack 2880 12 (LyFTP.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound LyFTP.all 0 (by norm_num)
  rw [Nat.mul_zero, ← LyFTP.eq] at h
  exact h

theorem gen_eq : lyFiveGenArr = CFSG.KS.Raw.unpack 2880 12 (LyFTG.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound LyFTG.all 0 (by norm_num)
  rw [Nat.mul_zero, ← LyFTG.eq] at h
  exact h

theorem a_eq : fiveArr4 lyFiveAbar = dec D.G0 := by decide +kernel

theorem b_eq : fiveArr4 lyFiveBbar = dec D.G1 := by decide +kernel

theorem i_eq : fiveArr4 1 = dec id4K := by decide +kernel

theorem nodup : lyFiveTbArr.toList.Nodup := tb_nodup a_eq b_eq i_eq par_eq gen_eq tb srt

end CertificateChecks.KernelSporSch.LyFT

end
