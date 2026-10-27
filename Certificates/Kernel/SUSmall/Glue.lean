module

public import Certificates.Kernel.SUSmall.Chk
public import CFSG.Certificates.Kernel.SUSmall.Sound
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs

public section

namespace CFSG.KD.SUSmall

open CFSG.KC.SUSmall Certificates.SUSmall CFSG.StandardType.HdRo7SU.Small

theorem leaf1597001 : SMClassSetLeaf := by
  rw [SMClassSetLeaf]
  exact ⟨fun _ hR => class_sound_wit (by norm_num) cat7 K7 33 NW7 OW7 SV7 DV7 AL7 smAllowed7
      cat7_ok none7_ok out7_ok surv7_ok subs7_ok al7_ok cover7_ok hR,
    fun _ hR => class_sound_wit (by norm_num) cat8 K8 44 NW8 OW8 SV8 DV8 AL8 smAllowed8
      cat8_ok none8_ok out8_ok surv8_ok subs8_ok al8_ok cover8_ok hR⟩

end CFSG.KD.SUSmall

end
