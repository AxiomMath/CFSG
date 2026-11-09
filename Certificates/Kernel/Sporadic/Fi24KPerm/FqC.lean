module

public import Certificates.Kernel.Sporadic.Fi24KPerm.FqL

set_option Elab.async false
set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24Sev
  CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem fqA46 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 46)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 46)).2 b)) cb = true := by
  decide +kernel

theorem fqP46a : fqP (nat_lit 46) (nat_lit 0) = true := fqP_all fqA46 (by decide)

theorem fqP46b : fqP (nat_lit 46) (nat_lit 305530) = true := fqP_all fqA46 (by decide)

theorem fqP46c : fqP (nat_lit 46) (nat_lit 5604) = true := fqP_all fqA46 (by decide)

theorem fqP46d : fqP (nat_lit 46) (nat_lit 221549) = true := fqP_all fqA46 (by decide)

theorem fqP46e : fqP (nat_lit 46) (nat_lit 266275) = true := fqP_all fqA46 (by decide)

theorem fqP46f : fqP (nat_lit 46) (nat_lit 186844) = true := fqP_all fqA46 (by decide)

theorem fqA47 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 47)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 47)).2 b)) cb = true := by
  decide +kernel

theorem fqP47a : fqP (nat_lit 47) (nat_lit 0) = true := fqP_all fqA47 (by decide)

theorem fqP47b : fqP (nat_lit 47) (nat_lit 305530) = true := fqP_all fqA47 (by decide)

theorem fqP47c : fqP (nat_lit 47) (nat_lit 5604) = true := fqP_all fqA47 (by decide)

theorem fqP47d : fqP (nat_lit 47) (nat_lit 221549) = true := fqP_all fqA47 (by decide)

theorem fqP47e : fqP (nat_lit 47) (nat_lit 266275) = true := fqP_all fqA47 (by decide)

theorem fqP47f : fqP (nat_lit 47) (nat_lit 186844) = true := fqP_all fqA47 (by decide)

theorem fqA48 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 48)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 48)).2 b)) cb = true := by
  decide +kernel

theorem fqP48a : fqP (nat_lit 48) (nat_lit 0) = true := fqP_all fqA48 (by decide)

theorem fqP48b : fqP (nat_lit 48) (nat_lit 305530) = true := fqP_all fqA48 (by decide)

theorem fqP48c : fqP (nat_lit 48) (nat_lit 5604) = true := fqP_all fqA48 (by decide)

theorem fqP48d : fqP (nat_lit 48) (nat_lit 221549) = true := fqP_all fqA48 (by decide)

theorem fqP48e : fqP (nat_lit 48) (nat_lit 266275) = true := fqP_all fqA48 (by decide)

theorem fqP48f : fqP (nat_lit 48) (nat_lit 186844) = true := fqP_all fqA48 (by decide)

theorem fqA49 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 49)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 49)).2 b)) cb = true := by
  decide +kernel

theorem fqP49a : fqP (nat_lit 49) (nat_lit 0) = true := fqP_all fqA49 (by decide)

theorem fqP49b : fqP (nat_lit 49) (nat_lit 305530) = true := fqP_all fqA49 (by decide)

theorem fqP49c : fqP (nat_lit 49) (nat_lit 5604) = true := fqP_all fqA49 (by decide)

theorem fqP49d : fqP (nat_lit 49) (nat_lit 221549) = true := fqP_all fqA49 (by decide)

theorem fqP49e : fqP (nat_lit 49) (nat_lit 266275) = true := fqP_all fqA49 (by decide)

theorem fqP49f : fqP (nat_lit 49) (nat_lit 186844) = true := fqP_all fqA49 (by decide)

theorem fqA50 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 50)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 50)).2 b)) cb = true := by
  decide +kernel

theorem fqP50a : fqP (nat_lit 50) (nat_lit 0) = true := fqP_all fqA50 (by decide)

theorem fqP50b : fqP (nat_lit 50) (nat_lit 305530) = true := fqP_all fqA50 (by decide)

theorem fqP50c : fqP (nat_lit 50) (nat_lit 5604) = true := fqP_all fqA50 (by decide)

theorem fqP50d : fqP (nat_lit 50) (nat_lit 221549) = true := fqP_all fqA50 (by decide)

theorem fqP50e : fqP (nat_lit 50) (nat_lit 266275) = true := fqP_all fqA50 (by decide)

theorem fqP50f : fqP (nat_lit 50) (nat_lit 186844) = true := fqP_all fqA50 (by decide)

theorem fqA51 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 51)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 51)).2 b)) cb = true := by
  decide +kernel

theorem fqP51a : fqP (nat_lit 51) (nat_lit 0) = true := fqP_all fqA51 (by decide)

theorem fqP51b : fqP (nat_lit 51) (nat_lit 305530) = true := fqP_all fqA51 (by decide)

theorem fqP51c : fqP (nat_lit 51) (nat_lit 5604) = true := fqP_all fqA51 (by decide)

theorem fqP51d : fqP (nat_lit 51) (nat_lit 221549) = true := fqP_all fqA51 (by decide)

theorem fqP51e : fqP (nat_lit 51) (nat_lit 266275) = true := fqP_all fqA51 (by decide)

theorem fqP51f : fqP (nat_lit 51) (nat_lit 186844) = true := fqP_all fqA51 (by decide)

theorem fqA52 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 52)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 52)).2 b)) cb = true := by
  decide +kernel

theorem fqP52a : fqP (nat_lit 52) (nat_lit 0) = true := fqP_all fqA52 (by decide)

theorem fqP52b : fqP (nat_lit 52) (nat_lit 305530) = true := fqP_all fqA52 (by decide)

theorem fqP52c : fqP (nat_lit 52) (nat_lit 5604) = true := fqP_all fqA52 (by decide)

theorem fqP52d : fqP (nat_lit 52) (nat_lit 221549) = true := fqP_all fqA52 (by decide)

theorem fqP52e : fqP (nat_lit 52) (nat_lit 266275) = true := fqP_all fqA52 (by decide)

theorem fqP52f : fqP (nat_lit 52) (nat_lit 186844) = true := fqP_all fqA52 (by decide)

theorem fqA53 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 53)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 53)).2 b)) cb = true := by
  decide +kernel

theorem fqP53a : fqP (nat_lit 53) (nat_lit 0) = true := fqP_all fqA53 (by decide)

theorem fqP53b : fqP (nat_lit 53) (nat_lit 305530) = true := fqP_all fqA53 (by decide)

theorem fqP53c : fqP (nat_lit 53) (nat_lit 5604) = true := fqP_all fqA53 (by decide)

theorem fqP53d : fqP (nat_lit 53) (nat_lit 221549) = true := fqP_all fqA53 (by decide)

theorem fqP53e : fqP (nat_lit 53) (nat_lit 266275) = true := fqP_all fqA53 (by decide)

theorem fqP53f : fqP (nat_lit 53) (nat_lit 186844) = true := fqP_all fqA53 (by decide)

theorem fqA54 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 54)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 54)).2 b)) cb = true := by
  decide +kernel

theorem fqP54a : fqP (nat_lit 54) (nat_lit 0) = true := fqP_all fqA54 (by decide)

theorem fqP54b : fqP (nat_lit 54) (nat_lit 305530) = true := fqP_all fqA54 (by decide)

theorem fqP54c : fqP (nat_lit 54) (nat_lit 5604) = true := fqP_all fqA54 (by decide)

theorem fqP54d : fqP (nat_lit 54) (nat_lit 221549) = true := fqP_all fqA54 (by decide)

theorem fqP54e : fqP (nat_lit 54) (nat_lit 266275) = true := fqP_all fqA54 (by decide)

theorem fqP54f : fqP (nat_lit 54) (nat_lit 186844) = true := fqP_all fqA54 (by decide)

theorem fqA55 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 55)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 55)).2 b)) cb = true := by
  decide +kernel

theorem fqP55a : fqP (nat_lit 55) (nat_lit 0) = true := fqP_all fqA55 (by decide)

theorem fqP55b : fqP (nat_lit 55) (nat_lit 305530) = true := fqP_all fqA55 (by decide)

theorem fqP55c : fqP (nat_lit 55) (nat_lit 5604) = true := fqP_all fqA55 (by decide)

theorem fqP55d : fqP (nat_lit 55) (nat_lit 221549) = true := fqP_all fqA55 (by decide)

theorem fqP55e : fqP (nat_lit 55) (nat_lit 266275) = true := fqP_all fqA55 (by decide)

theorem fqP55f : fqP (nat_lit 55) (nat_lit 186844) = true := fqP_all fqA55 (by decide)

theorem fqA56 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 56)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 56)).2 b)) cb = true := by
  decide +kernel

theorem fqP56a : fqP (nat_lit 56) (nat_lit 0) = true := fqP_all fqA56 (by decide)

theorem fqP56b : fqP (nat_lit 56) (nat_lit 305530) = true := fqP_all fqA56 (by decide)

theorem fqP56c : fqP (nat_lit 56) (nat_lit 5604) = true := fqP_all fqA56 (by decide)

theorem fqP56d : fqP (nat_lit 56) (nat_lit 221549) = true := fqP_all fqA56 (by decide)

theorem fqP56e : fqP (nat_lit 56) (nat_lit 266275) = true := fqP_all fqA56 (by decide)

theorem fqP56f : fqP (nat_lit 56) (nat_lit 186844) = true := fqP_all fqA56 (by decide)

theorem fqA57 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 57)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 57)).2 b)) cb = true := by
  decide +kernel

theorem fqP57a : fqP (nat_lit 57) (nat_lit 0) = true := fqP_all fqA57 (by decide)

theorem fqP57b : fqP (nat_lit 57) (nat_lit 305530) = true := fqP_all fqA57 (by decide)

theorem fqP57c : fqP (nat_lit 57) (nat_lit 5604) = true := fqP_all fqA57 (by decide)

theorem fqP57d : fqP (nat_lit 57) (nat_lit 221549) = true := fqP_all fqA57 (by decide)

theorem fqP57e : fqP (nat_lit 57) (nat_lit 266275) = true := fqP_all fqA57 (by decide)

theorem fqP57f : fqP (nat_lit 57) (nat_lit 186844) = true := fqP_all fqA57 (by decide)

theorem fqA58 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 58)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 58)).2 b)) cb = true := by
  decide +kernel

theorem fqP58a : fqP (nat_lit 58) (nat_lit 0) = true := fqP_all fqA58 (by decide)

theorem fqP58b : fqP (nat_lit 58) (nat_lit 305530) = true := fqP_all fqA58 (by decide)

theorem fqP58c : fqP (nat_lit 58) (nat_lit 5604) = true := fqP_all fqA58 (by decide)

theorem fqP58d : fqP (nat_lit 58) (nat_lit 221549) = true := fqP_all fqA58 (by decide)

theorem fqP58e : fqP (nat_lit 58) (nat_lit 266275) = true := fqP_all fqA58 (by decide)

theorem fqP58f : fqP (nat_lit 58) (nat_lit 186844) = true := fqP_all fqA58 (by decide)

theorem fqA59 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 59)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 59)).2 b)) cb = true := by
  decide +kernel

theorem fqP59a : fqP (nat_lit 59) (nat_lit 0) = true := fqP_all fqA59 (by decide)

theorem fqP59b : fqP (nat_lit 59) (nat_lit 305530) = true := fqP_all fqA59 (by decide)

theorem fqP59c : fqP (nat_lit 59) (nat_lit 5604) = true := fqP_all fqA59 (by decide)

theorem fqP59d : fqP (nat_lit 59) (nat_lit 221549) = true := fqP_all fqA59 (by decide)

theorem fqP59e : fqP (nat_lit 59) (nat_lit 266275) = true := fqP_all fqA59 (by decide)

theorem fqP59f : fqP (nat_lit 59) (nat_lit 186844) = true := fqP_all fqA59 (by decide)

theorem fqA60 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 60)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 60)).2 b)) cb = true := by
  decide +kernel

theorem fqP60a : fqP (nat_lit 60) (nat_lit 0) = true := fqP_all fqA60 (by decide)

theorem fqP60b : fqP (nat_lit 60) (nat_lit 305530) = true := fqP_all fqA60 (by decide)

theorem fqP60c : fqP (nat_lit 60) (nat_lit 5604) = true := fqP_all fqA60 (by decide)

theorem fqP60d : fqP (nat_lit 60) (nat_lit 221549) = true := fqP_all fqA60 (by decide)

theorem fqP60e : fqP (nat_lit 60) (nat_lit 266275) = true := fqP_all fqA60 (by decide)

theorem fqP60f : fqP (nat_lit 60) (nat_lit 186844) = true := fqP_all fqA60 (by decide)

theorem fqA61 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 61)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 61)).2 b)) cb = true := by
  decide +kernel

theorem fqP61a : fqP (nat_lit 61) (nat_lit 0) = true := fqP_all fqA61 (by decide)

theorem fqP61b : fqP (nat_lit 61) (nat_lit 305530) = true := fqP_all fqA61 (by decide)

theorem fqP61c : fqP (nat_lit 61) (nat_lit 5604) = true := fqP_all fqA61 (by decide)

theorem fqP61d : fqP (nat_lit 61) (nat_lit 221549) = true := fqP_all fqA61 (by decide)

theorem fqP61e : fqP (nat_lit 61) (nat_lit 266275) = true := fqP_all fqA61 (by decide)

theorem fqP61f : fqP (nat_lit 61) (nat_lit 186844) = true := fqP_all fqA61 (by decide)

theorem fqA62 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 62)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 62)).2 b)) cb = true := by
  decide +kernel

theorem fqP62a : fqP (nat_lit 62) (nat_lit 0) = true := fqP_all fqA62 (by decide)

theorem fqP62b : fqP (nat_lit 62) (nat_lit 305530) = true := fqP_all fqA62 (by decide)

theorem fqP62c : fqP (nat_lit 62) (nat_lit 5604) = true := fqP_all fqA62 (by decide)

theorem fqP62d : fqP (nat_lit 62) (nat_lit 221549) = true := fqP_all fqA62 (by decide)

theorem fqP62e : fqP (nat_lit 62) (nat_lit 266275) = true := fqP_all fqA62 (by decide)

theorem fqP62f : fqP (nat_lit 62) (nat_lit 186844) = true := fqP_all fqA62 (by decide)

theorem fqA63 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 63)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 63)).2 b)) cb = true := by
  decide +kernel

theorem fqP63a : fqP (nat_lit 63) (nat_lit 0) = true := fqP_all fqA63 (by decide)

theorem fqP63b : fqP (nat_lit 63) (nat_lit 305530) = true := fqP_all fqA63 (by decide)

theorem fqP63c : fqP (nat_lit 63) (nat_lit 5604) = true := fqP_all fqA63 (by decide)

theorem fqP63d : fqP (nat_lit 63) (nat_lit 221549) = true := fqP_all fqA63 (by decide)

theorem fqP63e : fqP (nat_lit 63) (nat_lit 266275) = true := fqP_all fqA63 (by decide)

theorem fqP63f : fqP (nat_lit 63) (nat_lit 186844) = true := fqP_all fqA63 (by decide)

theorem fqA64 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 64)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 64)).2 b)) cb = true := by
  decide +kernel

theorem fqP64a : fqP (nat_lit 64) (nat_lit 0) = true := fqP_all fqA64 (by decide)

theorem fqP64b : fqP (nat_lit 64) (nat_lit 305530) = true := fqP_all fqA64 (by decide)

theorem fqP64c : fqP (nat_lit 64) (nat_lit 5604) = true := fqP_all fqA64 (by decide)

theorem fqP64d : fqP (nat_lit 64) (nat_lit 221549) = true := fqP_all fqA64 (by decide)

theorem fqP64e : fqP (nat_lit 64) (nat_lit 266275) = true := fqP_all fqA64 (by decide)

theorem fqP64f : fqP (nat_lit 64) (nat_lit 186844) = true := fqP_all fqA64 (by decide)

theorem fqA65 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 65)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 65)).2 b)) cb = true := by
  decide +kernel

theorem fqP65a : fqP (nat_lit 65) (nat_lit 0) = true := fqP_all fqA65 (by decide)

theorem fqP65b : fqP (nat_lit 65) (nat_lit 305530) = true := fqP_all fqA65 (by decide)

theorem fqP65c : fqP (nat_lit 65) (nat_lit 5604) = true := fqP_all fqA65 (by decide)

theorem fqP65d : fqP (nat_lit 65) (nat_lit 221549) = true := fqP_all fqA65 (by decide)

theorem fqP65e : fqP (nat_lit 65) (nat_lit 266275) = true := fqP_all fqA65 (by decide)

theorem fqP65f : fqP (nat_lit 65) (nat_lit 186844) = true := fqP_all fqA65 (by decide)

theorem fqA66 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 66)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 66)).2 b)) cb = true := by
  decide +kernel

theorem fqP66a : fqP (nat_lit 66) (nat_lit 0) = true := fqP_all fqA66 (by decide)

theorem fqP66b : fqP (nat_lit 66) (nat_lit 305530) = true := fqP_all fqA66 (by decide)

theorem fqP66c : fqP (nat_lit 66) (nat_lit 5604) = true := fqP_all fqA66 (by decide)

theorem fqP66d : fqP (nat_lit 66) (nat_lit 221549) = true := fqP_all fqA66 (by decide)

theorem fqP66e : fqP (nat_lit 66) (nat_lit 266275) = true := fqP_all fqA66 (by decide)

theorem fqP66f : fqP (nat_lit 66) (nat_lit 186844) = true := fqP_all fqA66 (by decide)

theorem fqA67 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 67)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 67)).2 b)) cb = true := by
  decide +kernel

theorem fqP67a : fqP (nat_lit 67) (nat_lit 0) = true := fqP_all fqA67 (by decide)

theorem fqP67b : fqP (nat_lit 67) (nat_lit 305530) = true := fqP_all fqA67 (by decide)

theorem fqP67c : fqP (nat_lit 67) (nat_lit 5604) = true := fqP_all fqA67 (by decide)

theorem fqP67d : fqP (nat_lit 67) (nat_lit 221549) = true := fqP_all fqA67 (by decide)

theorem fqP67e : fqP (nat_lit 67) (nat_lit 266275) = true := fqP_all fqA67 (by decide)

theorem fqP67f : fqP (nat_lit 67) (nat_lit 186844) = true := fqP_all fqA67 (by decide)

theorem fqA68 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 68)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 68)).2 b)) cb = true := by
  decide +kernel

theorem fqP68a : fqP (nat_lit 68) (nat_lit 0) = true := fqP_all fqA68 (by decide)

theorem fqP68b : fqP (nat_lit 68) (nat_lit 305530) = true := fqP_all fqA68 (by decide)

theorem fqP68c : fqP (nat_lit 68) (nat_lit 5604) = true := fqP_all fqA68 (by decide)

theorem fqP68d : fqP (nat_lit 68) (nat_lit 221549) = true := fqP_all fqA68 (by decide)

theorem fqP68e : fqP (nat_lit 68) (nat_lit 266275) = true := fqP_all fqA68 (by decide)

theorem fqP68f : fqP (nat_lit 68) (nat_lit 186844) = true := fqP_all fqA68 (by decide)

end CFSG.KD.Fi24KPerm.Ck

end
