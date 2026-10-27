module

public import Certificates.Kernel.FiveTwo.F2
public import Certificates.Kernel.FiveTwo.F3
public import Certificates.Kernel.FiveTwo.F5
public import CFSG.Certificates.Kernel.FiveTwoKSound
public import Certificates.Kernel.TcGen.F5Glue
public import Certificates.Kernel.MatCert.GlueLy
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFT

open CFSG.KC.FiveTwoK CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.RankThree.Native CFSG.SectionRank.Native
  CFSG.Blueprint

theorem dec2 {d M : Nat} {cs : List Char} {s : String} (e : s = String.ofList cs)
    (h : CFSG.KC.M1F2.m1Bind cs d M = true) :
    (ops2 d).decode s = CFSG.KC.Co1F2.unpackR d M := by
  rw [e]
  exact CFSG.KC.Co1F2.bind_sound h

theorem j3 : FiveTwoData.check (ops2 80) j3FiveTwo = true :=
  check_of_fiveN (hom2 80 (by norm_num))
    (dec2 ((rfl : j3FiveTwo.base.seedA = NativeSporadic.J3Seed1).trans J3A.eq) J3A.bind)
    (dec2 ((rfl : j3FiveTwo.base.seedB = NativeSporadic.J3Seed2).trans J3B.eq) J3B.bind)
    trivial trivial j3_K

theorem co1 : FiveTwoData.check (ops2 24) co1FiveTwo = true :=
  check_of_fiveN (hom2 24 (by norm_num))
    (dec2 ((rfl : co1FiveTwo.base.seedA = NativeSporadic.Co1Seed1).trans KernelAM.C1A.eq)
      KernelAM.C1A.bind)
    (dec2 ((rfl : co1FiveTwo.base.seedB = NativeSporadic.Co1Seed2).trans KernelAM.C1B.eq)
      KernelAM.C1B.bind)
    trivial trivial co1_K

theorem co2 : FiveTwoData.check (ops2 22) co2FiveTwo = true :=
  check_of_fiveN (hom2 22 (by norm_num))
    (dec2 ((rfl : co2FiveTwo.base.seedA = NativeSporadic.Co2Seed1).trans KernelAM.C2A.eq)
      KernelAM.C2A.bind)
    (dec2 ((rfl : co2FiveTwo.base.seedB = NativeSporadic.Co2Seed2).trans KernelAM.C2B.eq)
      KernelAM.C2B.bind)
    trivial trivial co2_K

theorem co3 : FiveTwoData.check (ops2 22) co3FiveTwo = true :=
  check_of_fiveN (hom2 22 (by norm_num))
    (dec2 ((rfl : co3FiveTwo.base.seedA = NativeSporadic.Co3Seed1).trans KernelAM.C3A.eq)
      KernelAM.C3A.bind)
    (dec2 ((rfl : co3FiveTwo.base.seedB = NativeSporadic.Co3Seed2).trans KernelAM.C3B.eq)
      KernelAM.C3B.bind)
    trivial trivial co3_K

theorem hs : FiveTwoData.check (ops2 20) hsFiveTwo = true :=
  check_of_fiveN (hom2 20 (by norm_num))
    (dec2 ((rfl : hsFiveTwo.base.seedA = NativeSporadic.HSSeed1).trans KernelSRHS.SA.eq)
      KernelSRHS.SA.bind)
    (dec2 ((rfl : hsFiveTwo.base.seedB = NativeSporadic.HSSeed2).trans KernelSRHS.SB.eq)
      KernelSRHS.SB.bind)
    trivial trivial hs_K

theorem th : FiveTwoData.check (ops2 248) thFiveTwo = true :=
  check_of_fiveN (hom2 248 (by norm_num))
    (dec2 ((rfl : thFiveTwo.base.seedA = KernelLC.thSeedA).trans KernelLC.ThA.eq)
      KernelLC.ThA.bind)
    (dec2 ((rfl : thFiveTwo.base.seedB = KernelLC.thSeedB).trans KernelLC.ThB.eq)
      KernelLC.ThB.bind)
    trivial trivial th_K

theorem mcl : FiveTwoData.check (ops3 21) mclFiveTwo = true :=
  check_of_fiveL KernelTc.McL.lay_ok rfl rfl KernelTc.McL.decA KernelTc.McL.decB
    ((rfl : mclFiveTwo.base.seedA = NativeSporadic.McLSeed1).trans KernelTc.McL.LA_eq)
    ((rfl : mclFiveTwo.base.seedB = NativeSporadic.McLSeed2).trans KernelTc.McL.LB_eq) mcl_K

theorem suz : FiveTwoData.check (ops3 64) suzFiveTwo = true :=
  check_of_fiveL KernelTc.Suz.lay_ok rfl rfl KernelTc.Suz.decA KernelTc.Suz.decB
    ((rfl : suzFiveTwo.base.seedA = NativeSporadic.SuzSeed1).trans KernelTc.Suz.LA_eq)
    ((rfl : suzFiveTwo.base.seedB = NativeSporadic.SuzSeed2).trans KernelTc.Suz.LB_eq) suz_K

theorem on : FiveTwoData.check (ops3 154) onFiveTwo = true :=
  check_of_fiveL KernelTc.ON.lay_ok rfl rfl KernelTc.ON.decA KernelTc.ON.decB
    ((rfl : onFiveTwo.base.seedA = NativeSporadic.ONSeed1).trans KernelTc.ON.LA_eq)
    ((rfl : onFiveTwo.base.seedB = NativeSporadic.ONSeed2).trans KernelTc.ON.LB_eq) on_K

theorem hn : FiveTwoData.check (opsP 5 133) hnFiveTwo = true :=
  check_of_fiveN (homP KernelTc.HN.consts (by decide))
    ((congrArg _ (rfl : hnFiveTwo.base.seedA = NativeSporadic.HNSeed1)).trans KernelTc.HN.rowsA)
    ((congrArg _ (rfl : hnFiveTwo.base.seedB = NativeSporadic.HNSeed2)).trans KernelTc.HN.rowsB)
    KernelTc.HN.pay.2.2.1 KernelTc.HN.pay.2.2.2 hn_K

theorem ly : FiveTwoData.check (opsP 5 111) lyFiveTwo = true :=
  check_of_fiveN KernelMC.HL
    ((congrArg _ (rfl : lyFiveTwo.base.seedA = NativeSporadic.LySeed1)).trans KernelMC.lyA)
    ((congrArg _ (rfl : lyFiveTwo.base.seedB = NativeSporadic.LySeed2)).trans KernelMC.lyB)
    (KernelMC.vldL KernelSporSch.LyBS.vA) (KernelMC.vldL KernelSporSch.LyBS.vB) ly_K

end CertificateChecks.KernelFT

end
