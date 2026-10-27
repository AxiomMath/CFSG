module

public import Certificates.Kernel.M24G.FuseOrb
public import Certificates.Kernel.M24G.FuseInvChecks
public import Certificates.Kernel.M24G.KzeroChecks
public import CFSG.Certificates.Kernel.M24G.FuseInvSound
import CFSG.Certificates.Kernel.M24G.ReplayFacts

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem fuseInvLoop_ok : Native.fuseInvLoop (Native.kzeroSyl ()).1
    (Native.fuseOrbit Native.fusePiATab).1.toList
    (Native.fuseOrbit Native.fusePiBTab).1.toList = true := by
  rw [kzeroSyl_eq KzeroC.kzeroSyl_ok]
  exact fuseInvLoop_of (kz_LV KzeroC.kzeroSyl_ok) (replay_facts replayA).1
    (replay_facts replayB).1 mem_fuseOrbA mem_fuseOrbB fuseInv_okF

theorem fuseInvCheck_ok : Native.fuseInvCheck () = true := by
  unfold Native.fuseInvCheck
  simp only [fuseTreeA, fuseTreeB, fuseInvLoop_ok, Bool.and_self]

theorem fusePiCheck_ok : Native.fusePiCheck () = true := by
  unfold Native.fusePiCheck
  simp only [kzeroK0List_eq KzeroC.kzeroSyl_ok KzeroC.kzeroK0_ok]
  decide +kernel

end CFSG.KC.M24G.FuseC
