module

public import Certificates.Kernel.LocalQT.HS4089.T
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.Quasithin.Background.A312SporHSInputs

public section

namespace CFSG.KD.HSA312

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Vol2Native.L239.HSPairs (hsW1 hsW2)
open CFSG.KD.LQT.H4089 (letT powT)

def cpT : Array (Array Nat) :=
  let L1 := letT hsW1
  let L2 := letT hsW2
  let V1 := (Array.range 64).map fun i => wordTabA L1 1100 (CFSG.Quasithin.A312Hs.hsV1Word i)
  let V2 := (Array.range 64).map fun i => wordTabA L2 1100 (CFSG.Quasithin.A312Hs.hsV2Word i)
  let z4 := wordTabA L1 1100 CFSG.Quasithin.A312S.HS.hsZ4Word
  let es := (CFSG.Quasithin.A312S.HS.hsEWords.map (wordTabA L1 1100)).toArray
  let ws := (CFSG.Quasithin.A312S.HS.hsWWords.map (wordTabA L2 1100)).toArray
  let vs := (CFSG.Quasithin.A312S.HS.hsVWords.map (wordTabA L2 1100)).toArray
  let rs := CFSG.Quasithin.A312S.HS.hsQuot2.map (quotGt 1100 L2.toList)
  let ks := CFSG.Quasithin.A312S.HS.hsKer.map (CFSG.Quasithin.A312S.kerGt 1100 rs)
  let kis := CFSG.Quasithin.A312S.HS.hsKer.map (CFSG.Quasithin.A312S.kerGi 1100 rs)
  V1 ++ V2 ++ #[z4] ++ es ++ #[powT z4 2, powT z4 3] ++ es.map (fun e => powT e 3) ++ ws ++
    ws.map (fun w => powT w 3) ++ vs ++ rs.toArray ++ ks.toArray ++ kis.toArray

def cpQp : List (Nat × Nat) := []

end CFSG.KD.HSA312

end
