module

public import Certificates.Kernel.Sporadic.Fi24Sev.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF1 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF1.bin" 38367 11833947583908656342
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF2 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF2.bin" 38367 10822739123637325767
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF3 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF3.bin" 38367 11314968384040289903
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF4 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF4.bin" 38367 4155447072275101492
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF5 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF5.bin" 38367 3162540193106990832
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF6 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF6.bin" 38367 5589655593051426773
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBF7 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBF7.bin" 38367 16658932081042379434
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT1 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT1.bin" 38367 7852977310361408540
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT2 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT2.bin" 38367 8363621035143464052
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT3 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT3.bin" 38367 1749608624522597932
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT4 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT4.bin" 38367 12997409066584261046
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT5 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT5.bin" 38367 14702903823259556840
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT6 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT6.bin" 38367 10729198686677527152
#kc_repo #kc_natBin CFSG.KD.Fi24Sev covBT7 "Certificates/Kernel/Sporadic/Fi24Sev/data/covBT7.bin" 38367 16159951777965324551

public section

namespace CFSG.KD.Fi24Sev.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24Sev

theorem covB_f1 : Nat.beq (sweepW NW NT wsB (Nat.shiftLeft (nat_lit 1) omB)) covBF1 = true := by
  quickRfl

theorem covB_f2 : Nat.beq (sweepW NW NT wsB covBF1) covBF2 = true := by quickRfl

theorem covB_f3 : Nat.beq (sweepW NW NT wsB covBF2) covBF3 = true := by quickRfl

theorem covB_f4 : Nat.beq (sweepW NW NT wsB covBF3) covBF4 = true := by quickRfl

theorem covB_f5 : Nat.beq (sweepW NW NT wsB covBF4) covBF5 = true := by quickRfl

theorem covB_f6 : Nat.beq (sweepW NW NT wsB covBF5) covBF6 = true := by quickRfl

theorem covB_f7 : Nat.beq (sweepW NW NT wsB covBF6) covBF7 = true := by quickRfl

theorem covB_t1 : Nat.beq (sweepW NW NT wsB (plOf repsB)) covBT1 = true := by quickRfl

theorem covB_t2 : Nat.beq (sweepW NW NT wsB covBT1) covBT2 = true := by quickRfl

theorem covB_t3 : Nat.beq (sweepW NW NT wsB covBT2) covBT3 = true := by quickRfl

theorem covB_t4 : Nat.beq (sweepW NW NT wsB covBT3) covBT4 = true := by quickRfl

theorem covB_t5 : Nat.beq (sweepW NW NT wsB covBT4) covBT5 = true := by quickRfl

theorem covB_t6 : Nat.beq (sweepW NW NT wsB covBT5) covBT6 = true := by quickRfl

theorem covB_t7 : Nat.beq (sweepW NW NT wsB covBT6) covBT7 = true := by quickRfl

theorem covB_fin : andB (Nat.beq (Nat.land (Nat.lor covBT7 covBF7) ptsM) ptsM)
    (Nat.beq (popcount covBF7 (nat_lit 524288)) szB) = true := by quickRfl

theorem covB_t : CFSG.KD.Fi24Sev.covB = true := by
  have f := sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_step
    (sweepsW_step (sweepsW_one covB_f1) covB_f2) covB_f3) covB_f4) covB_f5) covB_f6) covB_f7
  have t := sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_step (sweepsW_step
    (sweepsW_step (sweepsW_one covB_t1) covB_t2) covB_t3) covB_t4) covB_t5) covB_t6) covB_t7
  exact covOK_of f t covB_fin

end CFSG.KD.Fi24Sev.Ck

end
