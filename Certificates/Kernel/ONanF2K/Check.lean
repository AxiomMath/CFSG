module

public import Certificates.Data.Kernel.ONanF2K.Defs
import all Certificates.Data.ONanF2Quot

public section

namespace CFSG.KC.ONanF2K

open CFSG.OddStandard.ONanRec.F2 AlpE CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def gP0 : List Nat := [16, 4, 1, 128, 256]

theorem expK_true : expK = true := by decide +kernel

theorem genMax1_beq : (genMaxE 1 == gP0.map decN) = true := by decide +kernel

theorem p0_beq : (ballMaxL.getD 1 [] == (unpackL P0T 256).map decN) = true := by decide +kernel

theorem n_beq : (ballNE == (unpackL NT 4).map decN) = true := by decide +kernel

theorem q8_beq : (ballQ8E == (unpackL Q8T 32).map decN) = true := by decide +kernel

theorem fE_all : ((List.range 512).all fun c => fE (decN c) == tcDec (lane fT c 6)) = true := by
  decide +kernel

theorem elts_beq : (xE == decN 27 && stE == decN 320) = true := by decide +kernel

theorem p0_len : (unpackL P0T 256).length = 256 := by decide +kernel

theorem p0_nodup : (unpackL P0T 256).Nodup := by decide +kernel

theorem p0_closed : ((unpackL P0T 256).all fun c => gP0.all fun g =>
    (unpackL P0T 256).contains (mulK c g % 512)) = true := by decide +kernel

theorem p0_conjx : ((List.range 512).all fun c =>
    (unpackL NT 4).contains (mulK (mulK c 27) (invK c) % 512)) = true := by decide +kernel

theorem p0_hom : ((unpackL P0T 256).all fun c => gP0.all fun g =>
    tcDec (lane fT (mulK c g % 512) 6) == tcDec (lane fT c 6) * tcDec (lane fT g 6)) = true := by
  decide +kernel

theorem p0_ker : ((unpackL P0T 256).all fun c =>
    (tcDec (lane fT c 6) == 1) == (unpackL NT 4).contains c) = true := by decide +kernel

theorem p0_surj : ((List.range 64).all fun k =>
    (unpackL P0T 256).any fun c => Nat.beq (lane fT c 6) k) = true := by decide +kernel

theorem tc_surj : ∀ y : TcM, ∃ k ∈ List.range 64, tcDec k = y := by decide +kernel

theorem p0_q8 : ((unpackL P0T 256).all fun c =>
    (unpackL NT 4).contains (mulK (invK (mulK c 320)) (mulK 320 c) % 512) ==
      (unpackL Q8T 32).contains c) = true := by decide +kernel

theorem factT_true : decide factT = true := by decide +kernel

end CFSG.KC.ONanF2K
