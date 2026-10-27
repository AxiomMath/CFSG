module

public import Certificates.Kernel.Misc.Perm.J2Mult5
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2M5

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.KFacts.KS14 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)

theorem enum_proved : enumOK 315 gensE25 keyPts cE25 = true :=
  enumK_sound' (G := GE) (PT := HP.F) (by quickRfl) (by decide) (by decide +kernel) gens_get
    (by decide +kernel) pts_get
    (fun i hi => ⟨by revert i; decide +kernel, fun _ _ => rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    e_head e_points e_keys

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS14 CFSG.Blueprint CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
open Certificates in
theorem facts_proved : chkMult5 = true := by
  have hsz : cE25.pts.size = 25 := by
    change cE25Lit.pts.size = 25
    simp [cE25Lit]
  unfold chkMult5
  rw [okx, oky, okg, x5, xy, gx, gy, enum_proved, hsz]
  rfl

end CertificateChecks.KernelMisc.J2M5

end
