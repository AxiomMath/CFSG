module

public import Certificates.Kernel.LocalComp.E8Gen
public import CFSG.Certificates.Kernel.LocalCompE8Sound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

set_option maxRecDepth 400000

#lc_e8 CertificateChecks.KernelLC.E8

namespace CertificateChecks.KernelLC.E8

open CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem refl_eq (r : Nat) (hr : r < 240) : reflArr r = unpack 240 8 (RT r) := by
  rw [CFSG.KLC.E8.reflArr_eq]
  exact (CFSG.KLC.E8.tables_sound bind sorted hrt neg).1 r hr

theorem neg_eq : negArr = unpack 240 8 NEG := by
  rw [CFSG.KLC.E8.negArr_eq]
  exact (CFSG.KLC.E8.tables_sound bind sorted hrt neg).2

theorem sign_eq (m : Nat) (hm : m < 256) (he : framePop m % 2 = 0) :
    signArr (frameDecode m) = unpack 240 8 (ST m) := by
  rw [CFSG.KLC.E8.signArr_eq]
  exact CFSG.KLC.E8.signs_sound bind sorted hst m hm he

end CertificateChecks.KernelLC.E8

end
