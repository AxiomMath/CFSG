module

public import Certificates.Kernel.SporSch.HeThree.C0Words
public import Certificates.Kernel.SporSch.HeThree.Facts
public import Certificates.Data.B3Spor3.HeWords
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

theorem c0Words : heC0WordsCheck = true := by
  have hw : szOK 8330 14 = true := by decide +kernel
  obtain ⟨hs, hb⟩ := bindC
  have hid : permB 8330 14 (pidn 8330 14) = true := permB_of_pp (CFSG.KC.BfsPin.PP.id hw)
  have p12 := permB_pcomp hw kC1 kC2
  have p122 := permB_pcomp hw p12 kC2
  have p11 := permB_pcomp hw kC1 kC1
  have p112 := permB_pcomp hw p11 kC2
  unfold heC0WordsCheck heC0Words
  rw [hs, hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num),
    CFSG.KC.BfsPin.validA_unpack kC0, CFSG.KC.BfsPin.validA_unpack kC1,
    CFSG.KC.BfsPin.validA_unpack kC2, comp_unpack hw kC1 kC2, comp_unpack hw p12 kC2,
    comp_unpack hw kC1 kC1, comp_unpack hw p11 kC2, pow_unpack hw kC0, pow_unpack hw p122,
    pow_unpack hw p112, CFSG.KC.BfsPin.idA_eq hw, eqA_unpack hw (permB_ppow hw kC0 3) hid,
    eqA_unpack hw (permB_ppow hw p122 12) hid, eqA_unpack hw (permB_ppow hw p112 12) hid, kW1, kW2,
    kW3]
  rfl

end CertificateChecks.KernelSporSch.HeThree

end
