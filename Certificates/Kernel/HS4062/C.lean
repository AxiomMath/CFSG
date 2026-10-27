module

public import Certificates.Kernel.HS4062.Fam
public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS4062

open CFSG.KC.Enum CFSG.KS.Prim CFSG.KC.Kc3K

theorem canonA : canonK 3850 12 4095 46200 (TF 0) = true := by quickRfl

theorem bindA : allN 3850 (fun i => Nat.beq (pg 12 4095 (TF 0) i) (pg 12 4095 (TF 0) i)) = true := by
  quickRfl

theorem canonB : canonK 3850 12 4095 46200 (TF 1) = true := by quickRfl

theorem bindB : allN 3850 (fun i => Nat.beq (pg 12 4095 (TF 1) i) (pg 12 4095 (TF 1) i)) = true := by
  quickRfl

theorem eqA : Nat.beq (TF 0) (CFSG.KD.LQT.C4126.HS.F 0) = true := by quickRfl

theorem eqB : Nat.beq (TF 1) (CFSG.KD.LQT.C4126.HS.F 1) = true := by quickRfl

theorem valid : CFSG.QuasithinUnique.K1.SporadicPerm.slpValidAux progX 2 = true := by
  decide +kernel

theorem len : progX.length = 201 := by decide +kernel

theorem cls : (List.range 8).all (fun k => clsK 87 pr (EL k)) = true := by quickRfl

theorem conj : (List.range 3).all (fun t =>
    cjEK 12 4095 TF B vu vv (0 :: EL 5) (NG.getD t 0) (PI t)) = true := by
  quickRfl

theorem cl : clEK 12 4095 87 TF B vu vv (0 :: EL 5) RN CL (EM.getD 0 0) = true := by quickRfl

theorem fib : (List.range 8).all (fun k => maskL (EL k) == EM.getD k 0 && (EL k).length == 15 &&
    chainLt (EL k) && (EL k).all (fun i => decide (i < 87)) &&
    (decide (k = 0) || decide (k = 5) || fbK (fun i => (FL i).length) (EL k))) = true := by
  quickRfl

theorem emLen : EM.length = 8 := by decide +kernel

theorem fix : (fixE FL FM (EL 5)).length = 16 := by decide +kernel

theorem one : B.all (fun p => exK 12 4095 TF (eu 2) (ev 2) p == p) = true := by quickRfl

theorem gsLen : GS.length = 3 := by decide +kernel

theorem gsLt : ∀ g ∈ GS, g < 203 := by decide +kernel

theorem ngLt : ∀ g ∈ NG, g < 203 := by decide +kernel

theorem ngLen : NG.length = 3 := by decide +kernel

theorem rnLt : RN < 203 := by decide +kernel

end CFSG.KD.HS4062

end
