
module

public import Certificates.Data.Kernel.PermCent.L34ModelTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34Mod

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def sideC (S G : List (CV 42)) (y : CV 42) : Bool :=
  decide S.Nodup && decide ((1 : CV 42) ∈ S) && (G.all fun s => decide (s ∈ S)) &&
    powOneC y 3 && (S.all fun a => S.all fun b => decide (a * b ∈ S)) &&
    (S.all fun a => decide (a⁻¹ ∈ S)) && (S.all fun g => siftC QP g 0) && siftC QP y 0 &&
    (S.all fun s => decide (y * s * y⁻¹ ∈ S)) && (S.all fun s => !eq22C y s s y || decide (s = 1))

theorem kSide : sideC sC gS (cOf y0) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L34Mod

end
