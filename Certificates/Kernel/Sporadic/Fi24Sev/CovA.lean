module

public import Certificates.Kernel.Sporadic.Fi24Sev.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAF1 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAF1.bin" 38367 3300521090826129381
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAF2 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAF2.bin" 38367 17350233458706445134
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAF3 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAF3.bin" 38367 8037042183462319392
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAF4 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAF4.bin" 38367 4814552301639649837
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAT1 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAT1.bin" 38367 12383566593987764338
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAT2 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAT2.bin" 38367 10065200447371316467
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAT3 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAT3.bin" 38367 3436369490469992008
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covAT4 "Certificates/Kernel/Sporadic/Fi24Sev/data/covAT4.bin" 38367 8800288771294325192

public section

namespace CFSG.KD.Fi24Sev.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24Sev

theorem covA_f1 : Nat.beq (sweepW NW NT wsA (Nat.shiftLeft (nat_lit 1) omA)) covAF1 = true := by
  quickRfl

theorem covA_f2 : Nat.beq (sweepW NW NT wsA covAF1) covAF2 = true := by quickRfl

theorem covA_f3 : Nat.beq (sweepW NW NT wsA covAF2) covAF3 = true := by quickRfl

theorem covA_f4 : Nat.beq (sweepW NW NT wsA covAF3) covAF4 = true := by quickRfl

theorem covA_t1 : Nat.beq (sweepW NW NT wsA (plOf repsA)) covAT1 = true := by quickRfl

theorem covA_t2 : Nat.beq (sweepW NW NT wsA covAT1) covAT2 = true := by quickRfl

theorem covA_t3 : Nat.beq (sweepW NW NT wsA covAT2) covAT3 = true := by quickRfl

theorem covA_t4 : Nat.beq (sweepW NW NT wsA covAT3) covAT4 = true := by quickRfl

theorem covA_fin : andB (Nat.beq (Nat.land (Nat.lor covAT4 covAF4) ptsM) ptsM)
    (Nat.beq (popcount covAF4 (nat_lit 524288)) szA) = true := by quickRfl

theorem covA_t : CFSG.KD.Fi24Sev.covA = true := by
  have f := sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_one covA_f1) covA_f2) covA_f3) covA_f4
  have t := sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_one covA_t1) covA_t2) covA_t3) covA_t4
  exact covOK_of f t covA_fin

end CFSG.KD.Fi24Sev.Ck

end
