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

theorem factT_1 :
    SubOK genTE ballTE 64 := by
  decide +kernel

theorem factT_2 :
    SubOK genSE ballSE 8 := by
  decide +kernel

theorem factT_3 :
    SubOK genCTSE ballCTSE 8 := by
  decide +kernel

theorem factT_4 :
    mE ^ 8 = 1 ∧ mE ^ 4 ≠ 1 := by
  decide +kernel

theorem factT_5 :
    lE ^ 4 = 1 ∧ lE ^ 2 ≠ 1 := by
  decide +kernel

theorem factT_6 :
    stE ^ 2 = 1 ∧ stE ≠ 1 := by
  decide +kernel

theorem factT_7 :
    mE⁻¹ * lE * mE = lE⁻¹ := by
  decide +kernel

theorem factT_8 :
    stE⁻¹ * lE * stE = lE := by
  decide +kernel

theorem factT_9 :
    stE⁻¹ * mE * stE = mE ^ 3 * lE ^ 2 := by
  decide +kernel

theorem factT_10 :
    xE = lE ^ 2 * mE ^ 2 := by
  decide +kernel

theorem factT_11 :
    mE ^ 4 = zc := by
  decide +kernel

theorem factT_12 :
    xE ^ 4 = 1 := by
  decide +kernel

theorem factT_13 :
    xE ^ 2 ≠ 1 := by
  decide +kernel

theorem factT_14 :
    stE⁻¹ * xE * stE = xE⁻¹ := by
  decide +kernel

theorem factT_15 :
    ∀ t ∈ ballTE, ∀ s ∈ ballSE, t * s * t⁻¹ ∈ ballSE := by
  decide +kernel

theorem factT_16 :
    ∀ t ∈ ballTE, ((∀ s ∈ genSE, t * s = s * t) ↔ t ∈ ballCTSE) := by
  decide +kernel

theorem factT_17 :
    ∀ t ∈ ballCTSE, t ∈ ballSE → t = 1 ∨ t = zc := by
  decide +kernel

theorem factT_18 :
    ∀ y ∈ ballCTSE, y ^ 4 = 1 → y ^ 2 ≠ 1 → y ∈ zPrimes := by
  decide +kernel

theorem factT_19 :
    ∀ i : Fin 4, ZpOK (zPrimes.getD i 1) (ballZpL.getD i []) := by
  decide +kernel

theorem factT_20 :
    (mE * lE) ^ 4 ∈ ballSE ∧ (mE * lE) ^ 2 ∉ ballSE ∧ ((mE * lE) ^ 2)⁻¹ * lE ^ 2 ∈ ballSE ∧
      lE⁻¹ * (mE * lE) * lE * (mE * lE) ∈ ballSE := by
  decide +kernel

theorem factT_true : decide factT = true := by
  refine decide_eq_true ?_
  unfold factT
  exact ⟨factT_1, factT_2, factT_3, factT_4, factT_5, factT_6, factT_7, factT_8, factT_9, factT_10,
    factT_11, factT_12, factT_13, factT_14, factT_15, factT_16, factT_17, factT_18, factT_19,
    factT_20⟩

end CFSG.KC.ONanF2K
