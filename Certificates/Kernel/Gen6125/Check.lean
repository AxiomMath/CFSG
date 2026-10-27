module

public import Certificates.Kernel.Gen6125.Data
public import Certificates.Kernel.BalanceSC.Data
public import Certificates.Data.Kernel.Gen6125
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenInputs

public section

open CFSG.KC.Gen6125
open CFSG.KC.BalanceSC (getL tab64)
open CFSG.KC.Enum (pg)
open CFSG.OddStandard.Solomon75.AhatData (genGSw genWord swOK swapsA)

namespace CFSG.KD.G6125n8

theorem swG : (genGSw 8).all (fun sw => swOK 8 sw true) = true := by decide +kernel

theorem lenG : (genGSw 8).length = 3 := by decide +kernel

theorem bindG : ((List.range 3).all fun j => (List.range 8).all fun i =>
    Nat.beq ((swapsA 8 (genGSw 8)[j]!)[i]!) (pg 4 15 (getL 0 GG j) i)) = true := by
  decide +kernel

theorem ats : atsK 8 64 (tab64 CFSG.KD.BalSC8.PB) true GG IA IB IC = true := by decide +kernel

theorem word : wordK 8 GG (genWord 8) = true := by decide +kernel

theorem pairs : pairK 8 GG OC OP OL = true := by decide +kernel

end CFSG.KD.G6125n8

namespace CFSG.KD.G6125n11

theorem swG : (genGSw 11).all (fun sw => swOK 11 sw true) = true := by decide +kernel

theorem lenG : (genGSw 11).length = 3 := by decide +kernel

theorem bindG : ((List.range 3).all fun j => (List.range 11).all fun i =>
    Nat.beq ((swapsA 11 (genGSw 11)[j]!)[i]!) (pg 4 15 (getL 0 GG j) i)) = true := by
  decide +kernel

theorem ats : atsK 11 128 (tab64 CFSG.KD.BalSC11.PB) false GG IA IB IC = true := by
  decide +kernel

theorem word : wordK 11 GG (genWord 11) = true := by decide +kernel

theorem pairs : pairK 11 GG OC OP OL = true := by decide +kernel

end CFSG.KD.G6125n11

end
