module

public import Certificates.Data.Kernel.J4Mask11

public section

namespace CertificateChecks.KernelJ4Mask11

open CFSG.EvenSporadicStandard.J4Std.Data11 CFSG.KC.J4Mask11
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks)

theorem mf1 : ∀ j < 11, pWord.foldr act (2 ^ j) = pRow j := by decide +kernel

theorem mf2 : ∀ j < 11, pRow j < 2 ^ 11 := by decide +kernel

theorem mf3 : pMap 2 ≠ 2 := by decide +kernel

theorem mf4 : pMap u0Mask = u0Mask := by decide +kernel

theorem mf5 : ∀ c < 2 ^ 11, pMap c = c → c = 0 ∨ c = u0Mask := by decide +kernel

theorem mask6_ok : chkMask6 = true := by decide +kernel

theorem mask7_ok : chkMask7 = true := by decide +kernel

theorem mask8_ok : chkMask8 = true := by decide +kernel

theorem mask8w_ok : chkMask8w = true := by decide +kernel

end CertificateChecks.KernelJ4Mask11
