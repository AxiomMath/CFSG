module

public import Certificates.Kernel.Sporadic.Fi24KPerm.FqL

set_option Elab.async false
set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24Sev
  CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem fqA0 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 0)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 0)).2 b)) cb = true := by
  decide +kernel

theorem fqP0a : fqP (nat_lit 0) (nat_lit 0) = true := fqP_all fqA0 (by decide)

theorem fqP0b : fqP (nat_lit 0) (nat_lit 305530) = true := fqP_all fqA0 (by decide)

theorem fqP0c : fqP (nat_lit 0) (nat_lit 5604) = true := fqP_all fqA0 (by decide)

theorem fqP0d : fqP (nat_lit 0) (nat_lit 221549) = true := fqP_all fqA0 (by decide)

theorem fqP0e : fqP (nat_lit 0) (nat_lit 266275) = true := fqP_all fqA0 (by decide)

theorem fqP0f : fqP (nat_lit 0) (nat_lit 186844) = true := fqP_all fqA0 (by decide)

theorem fqA1 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 1)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 1)).2 b)) cb = true := by
  decide +kernel

theorem fqP1a : fqP (nat_lit 1) (nat_lit 0) = true := fqP_all fqA1 (by decide)

theorem fqP1b : fqP (nat_lit 1) (nat_lit 305530) = true := fqP_all fqA1 (by decide)

theorem fqP1c : fqP (nat_lit 1) (nat_lit 5604) = true := fqP_all fqA1 (by decide)

theorem fqP1d : fqP (nat_lit 1) (nat_lit 221549) = true := fqP_all fqA1 (by decide)

theorem fqP1e : fqP (nat_lit 1) (nat_lit 266275) = true := fqP_all fqA1 (by decide)

theorem fqP1f : fqP (nat_lit 1) (nat_lit 186844) = true := fqP_all fqA1 (by decide)

theorem fqA2 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 2)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 2)).2 b)) cb = true := by
  decide +kernel

theorem fqP2a : fqP (nat_lit 2) (nat_lit 0) = true := fqP_all fqA2 (by decide)

theorem fqP2b : fqP (nat_lit 2) (nat_lit 305530) = true := fqP_all fqA2 (by decide)

theorem fqP2c : fqP (nat_lit 2) (nat_lit 5604) = true := fqP_all fqA2 (by decide)

theorem fqP2d : fqP (nat_lit 2) (nat_lit 221549) = true := fqP_all fqA2 (by decide)

theorem fqP2e : fqP (nat_lit 2) (nat_lit 266275) = true := fqP_all fqA2 (by decide)

theorem fqP2f : fqP (nat_lit 2) (nat_lit 186844) = true := fqP_all fqA2 (by decide)

theorem fqA3 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 3)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 3)).2 b)) cb = true := by
  decide +kernel

theorem fqP3a : fqP (nat_lit 3) (nat_lit 0) = true := fqP_all fqA3 (by decide)

theorem fqP3b : fqP (nat_lit 3) (nat_lit 305530) = true := fqP_all fqA3 (by decide)

theorem fqP3c : fqP (nat_lit 3) (nat_lit 5604) = true := fqP_all fqA3 (by decide)

theorem fqP3d : fqP (nat_lit 3) (nat_lit 221549) = true := fqP_all fqA3 (by decide)

theorem fqP3e : fqP (nat_lit 3) (nat_lit 266275) = true := fqP_all fqA3 (by decide)

theorem fqP3f : fqP (nat_lit 3) (nat_lit 186844) = true := fqP_all fqA3 (by decide)

theorem fqA4 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 4)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 4)).2 b)) cb = true := by
  decide +kernel

theorem fqP4a : fqP (nat_lit 4) (nat_lit 0) = true := fqP_all fqA4 (by decide)

theorem fqP4b : fqP (nat_lit 4) (nat_lit 305530) = true := fqP_all fqA4 (by decide)

theorem fqP4c : fqP (nat_lit 4) (nat_lit 5604) = true := fqP_all fqA4 (by decide)

theorem fqP4d : fqP (nat_lit 4) (nat_lit 221549) = true := fqP_all fqA4 (by decide)

theorem fqP4e : fqP (nat_lit 4) (nat_lit 266275) = true := fqP_all fqA4 (by decide)

theorem fqP4f : fqP (nat_lit 4) (nat_lit 186844) = true := fqP_all fqA4 (by decide)

theorem fqA5 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 5)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 5)).2 b)) cb = true := by
  decide +kernel

theorem fqP5a : fqP (nat_lit 5) (nat_lit 0) = true := fqP_all fqA5 (by decide)

theorem fqP5b : fqP (nat_lit 5) (nat_lit 305530) = true := fqP_all fqA5 (by decide)

theorem fqP5c : fqP (nat_lit 5) (nat_lit 5604) = true := fqP_all fqA5 (by decide)

theorem fqP5d : fqP (nat_lit 5) (nat_lit 221549) = true := fqP_all fqA5 (by decide)

theorem fqP5e : fqP (nat_lit 5) (nat_lit 266275) = true := fqP_all fqA5 (by decide)

theorem fqP5f : fqP (nat_lit 5) (nat_lit 186844) = true := fqP_all fqA5 (by decide)

theorem fqA6 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 6)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 6)).2 b)) cb = true := by
  decide +kernel

theorem fqP6a : fqP (nat_lit 6) (nat_lit 0) = true := fqP_all fqA6 (by decide)

theorem fqP6b : fqP (nat_lit 6) (nat_lit 305530) = true := fqP_all fqA6 (by decide)

theorem fqP6c : fqP (nat_lit 6) (nat_lit 5604) = true := fqP_all fqA6 (by decide)

theorem fqP6d : fqP (nat_lit 6) (nat_lit 221549) = true := fqP_all fqA6 (by decide)

theorem fqP6e : fqP (nat_lit 6) (nat_lit 266275) = true := fqP_all fqA6 (by decide)

theorem fqP6f : fqP (nat_lit 6) (nat_lit 186844) = true := fqP_all fqA6 (by decide)

theorem fqA7 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 7)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 7)).2 b)) cb = true := by
  decide +kernel

theorem fqP7a : fqP (nat_lit 7) (nat_lit 0) = true := fqP_all fqA7 (by decide)

theorem fqP7b : fqP (nat_lit 7) (nat_lit 305530) = true := fqP_all fqA7 (by decide)

theorem fqP7c : fqP (nat_lit 7) (nat_lit 5604) = true := fqP_all fqA7 (by decide)

theorem fqP7d : fqP (nat_lit 7) (nat_lit 221549) = true := fqP_all fqA7 (by decide)

theorem fqP7e : fqP (nat_lit 7) (nat_lit 266275) = true := fqP_all fqA7 (by decide)

theorem fqP7f : fqP (nat_lit 7) (nat_lit 186844) = true := fqP_all fqA7 (by decide)

theorem fqA8 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 8)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 8)).2 b)) cb = true := by
  decide +kernel

theorem fqP8a : fqP (nat_lit 8) (nat_lit 0) = true := fqP_all fqA8 (by decide)

theorem fqP8b : fqP (nat_lit 8) (nat_lit 305530) = true := fqP_all fqA8 (by decide)

theorem fqP8c : fqP (nat_lit 8) (nat_lit 5604) = true := fqP_all fqA8 (by decide)

theorem fqP8d : fqP (nat_lit 8) (nat_lit 221549) = true := fqP_all fqA8 (by decide)

theorem fqP8e : fqP (nat_lit 8) (nat_lit 266275) = true := fqP_all fqA8 (by decide)

theorem fqP8f : fqP (nat_lit 8) (nat_lit 186844) = true := fqP_all fqA8 (by decide)

theorem fqA9 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 9)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 9)).2 b)) cb = true := by
  decide +kernel

theorem fqP9a : fqP (nat_lit 9) (nat_lit 0) = true := fqP_all fqA9 (by decide)

theorem fqP9b : fqP (nat_lit 9) (nat_lit 305530) = true := fqP_all fqA9 (by decide)

theorem fqP9c : fqP (nat_lit 9) (nat_lit 5604) = true := fqP_all fqA9 (by decide)

theorem fqP9d : fqP (nat_lit 9) (nat_lit 221549) = true := fqP_all fqA9 (by decide)

theorem fqP9e : fqP (nat_lit 9) (nat_lit 266275) = true := fqP_all fqA9 (by decide)

theorem fqP9f : fqP (nat_lit 9) (nat_lit 186844) = true := fqP_all fqA9 (by decide)

theorem fqA10 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 10)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 10)).2 b)) cb = true := by
  decide +kernel

theorem fqP10a : fqP (nat_lit 10) (nat_lit 0) = true := fqP_all fqA10 (by decide)

theorem fqP10b : fqP (nat_lit 10) (nat_lit 305530) = true := fqP_all fqA10 (by decide)

theorem fqP10c : fqP (nat_lit 10) (nat_lit 5604) = true := fqP_all fqA10 (by decide)

theorem fqP10d : fqP (nat_lit 10) (nat_lit 221549) = true := fqP_all fqA10 (by decide)

theorem fqP10e : fqP (nat_lit 10) (nat_lit 266275) = true := fqP_all fqA10 (by decide)

theorem fqP10f : fqP (nat_lit 10) (nat_lit 186844) = true := fqP_all fqA10 (by decide)

theorem fqA11 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 11)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 11)).2 b)) cb = true := by
  decide +kernel

theorem fqP11a : fqP (nat_lit 11) (nat_lit 0) = true := fqP_all fqA11 (by decide)

theorem fqP11b : fqP (nat_lit 11) (nat_lit 305530) = true := fqP_all fqA11 (by decide)

theorem fqP11c : fqP (nat_lit 11) (nat_lit 5604) = true := fqP_all fqA11 (by decide)

theorem fqP11d : fqP (nat_lit 11) (nat_lit 221549) = true := fqP_all fqA11 (by decide)

theorem fqP11e : fqP (nat_lit 11) (nat_lit 266275) = true := fqP_all fqA11 (by decide)

theorem fqP11f : fqP (nat_lit 11) (nat_lit 186844) = true := fqP_all fqA11 (by decide)

theorem fqA12 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 12)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 12)).2 b)) cb = true := by
  decide +kernel

theorem fqP12a : fqP (nat_lit 12) (nat_lit 0) = true := fqP_all fqA12 (by decide)

theorem fqP12b : fqP (nat_lit 12) (nat_lit 305530) = true := fqP_all fqA12 (by decide)

theorem fqP12c : fqP (nat_lit 12) (nat_lit 5604) = true := fqP_all fqA12 (by decide)

theorem fqP12d : fqP (nat_lit 12) (nat_lit 221549) = true := fqP_all fqA12 (by decide)

theorem fqP12e : fqP (nat_lit 12) (nat_lit 266275) = true := fqP_all fqA12 (by decide)

theorem fqP12f : fqP (nat_lit 12) (nat_lit 186844) = true := fqP_all fqA12 (by decide)

theorem fqA13 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 13)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 13)).2 b)) cb = true := by
  decide +kernel

theorem fqP13a : fqP (nat_lit 13) (nat_lit 0) = true := fqP_all fqA13 (by decide)

theorem fqP13b : fqP (nat_lit 13) (nat_lit 305530) = true := fqP_all fqA13 (by decide)

theorem fqP13c : fqP (nat_lit 13) (nat_lit 5604) = true := fqP_all fqA13 (by decide)

theorem fqP13d : fqP (nat_lit 13) (nat_lit 221549) = true := fqP_all fqA13 (by decide)

theorem fqP13e : fqP (nat_lit 13) (nat_lit 266275) = true := fqP_all fqA13 (by decide)

theorem fqP13f : fqP (nat_lit 13) (nat_lit 186844) = true := fqP_all fqA13 (by decide)

theorem fqA14 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 14)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 14)).2 b)) cb = true := by
  decide +kernel

theorem fqP14a : fqP (nat_lit 14) (nat_lit 0) = true := fqP_all fqA14 (by decide)

theorem fqP14b : fqP (nat_lit 14) (nat_lit 305530) = true := fqP_all fqA14 (by decide)

theorem fqP14c : fqP (nat_lit 14) (nat_lit 5604) = true := fqP_all fqA14 (by decide)

theorem fqP14d : fqP (nat_lit 14) (nat_lit 221549) = true := fqP_all fqA14 (by decide)

theorem fqP14e : fqP (nat_lit 14) (nat_lit 266275) = true := fqP_all fqA14 (by decide)

theorem fqP14f : fqP (nat_lit 14) (nat_lit 186844) = true := fqP_all fqA14 (by decide)

theorem fqA15 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 15)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 15)).2 b)) cb = true := by
  decide +kernel

theorem fqP15a : fqP (nat_lit 15) (nat_lit 0) = true := fqP_all fqA15 (by decide)

theorem fqP15b : fqP (nat_lit 15) (nat_lit 305530) = true := fqP_all fqA15 (by decide)

theorem fqP15c : fqP (nat_lit 15) (nat_lit 5604) = true := fqP_all fqA15 (by decide)

theorem fqP15d : fqP (nat_lit 15) (nat_lit 221549) = true := fqP_all fqA15 (by decide)

theorem fqP15e : fqP (nat_lit 15) (nat_lit 266275) = true := fqP_all fqA15 (by decide)

theorem fqP15f : fqP (nat_lit 15) (nat_lit 186844) = true := fqP_all fqA15 (by decide)

theorem fqA16 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 16)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 16)).2 b)) cb = true := by
  decide +kernel

theorem fqP16a : fqP (nat_lit 16) (nat_lit 0) = true := fqP_all fqA16 (by decide)

theorem fqP16b : fqP (nat_lit 16) (nat_lit 305530) = true := fqP_all fqA16 (by decide)

theorem fqP16c : fqP (nat_lit 16) (nat_lit 5604) = true := fqP_all fqA16 (by decide)

theorem fqP16d : fqP (nat_lit 16) (nat_lit 221549) = true := fqP_all fqA16 (by decide)

theorem fqP16e : fqP (nat_lit 16) (nat_lit 266275) = true := fqP_all fqA16 (by decide)

theorem fqP16f : fqP (nat_lit 16) (nat_lit 186844) = true := fqP_all fqA16 (by decide)

theorem fqA17 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 17)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 17)).2 b)) cb = true := by
  decide +kernel

theorem fqP17a : fqP (nat_lit 17) (nat_lit 0) = true := fqP_all fqA17 (by decide)

theorem fqP17b : fqP (nat_lit 17) (nat_lit 305530) = true := fqP_all fqA17 (by decide)

theorem fqP17c : fqP (nat_lit 17) (nat_lit 5604) = true := fqP_all fqA17 (by decide)

theorem fqP17d : fqP (nat_lit 17) (nat_lit 221549) = true := fqP_all fqA17 (by decide)

theorem fqP17e : fqP (nat_lit 17) (nat_lit 266275) = true := fqP_all fqA17 (by decide)

theorem fqP17f : fqP (nat_lit 17) (nat_lit 186844) = true := fqP_all fqA17 (by decide)

theorem fqA18 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 18)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 18)).2 b)) cb = true := by
  decide +kernel

theorem fqP18a : fqP (nat_lit 18) (nat_lit 0) = true := fqP_all fqA18 (by decide)

theorem fqP18b : fqP (nat_lit 18) (nat_lit 305530) = true := fqP_all fqA18 (by decide)

theorem fqP18c : fqP (nat_lit 18) (nat_lit 5604) = true := fqP_all fqA18 (by decide)

theorem fqP18d : fqP (nat_lit 18) (nat_lit 221549) = true := fqP_all fqA18 (by decide)

theorem fqP18e : fqP (nat_lit 18) (nat_lit 266275) = true := fqP_all fqA18 (by decide)

theorem fqP18f : fqP (nat_lit 18) (nat_lit 186844) = true := fqP_all fqA18 (by decide)

theorem fqA19 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 19)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 19)).2 b)) cb = true := by
  decide +kernel

theorem fqP19a : fqP (nat_lit 19) (nat_lit 0) = true := fqP_all fqA19 (by decide)

theorem fqP19b : fqP (nat_lit 19) (nat_lit 305530) = true := fqP_all fqA19 (by decide)

theorem fqP19c : fqP (nat_lit 19) (nat_lit 5604) = true := fqP_all fqA19 (by decide)

theorem fqP19d : fqP (nat_lit 19) (nat_lit 221549) = true := fqP_all fqA19 (by decide)

theorem fqP19e : fqP (nat_lit 19) (nat_lit 266275) = true := fqP_all fqA19 (by decide)

theorem fqP19f : fqP (nat_lit 19) (nat_lit 186844) = true := fqP_all fqA19 (by decide)

theorem fqA20 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 20)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 20)).2 b)) cb = true := by
  decide +kernel

theorem fqP20a : fqP (nat_lit 20) (nat_lit 0) = true := fqP_all fqA20 (by decide)

theorem fqP20b : fqP (nat_lit 20) (nat_lit 305530) = true := fqP_all fqA20 (by decide)

theorem fqP20c : fqP (nat_lit 20) (nat_lit 5604) = true := fqP_all fqA20 (by decide)

theorem fqP20d : fqP (nat_lit 20) (nat_lit 221549) = true := fqP_all fqA20 (by decide)

theorem fqP20e : fqP (nat_lit 20) (nat_lit 266275) = true := fqP_all fqA20 (by decide)

theorem fqP20f : fqP (nat_lit 20) (nat_lit 186844) = true := fqP_all fqA20 (by decide)

theorem fqA21 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 21)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 21)).2 b)) cb = true := by
  decide +kernel

theorem fqP21a : fqP (nat_lit 21) (nat_lit 0) = true := fqP_all fqA21 (by decide)

theorem fqP21b : fqP (nat_lit 21) (nat_lit 305530) = true := fqP_all fqA21 (by decide)

theorem fqP21c : fqP (nat_lit 21) (nat_lit 5604) = true := fqP_all fqA21 (by decide)

theorem fqP21d : fqP (nat_lit 21) (nat_lit 221549) = true := fqP_all fqA21 (by decide)

theorem fqP21e : fqP (nat_lit 21) (nat_lit 266275) = true := fqP_all fqA21 (by decide)

theorem fqP21f : fqP (nat_lit 21) (nat_lit 186844) = true := fqP_all fqA21 (by decide)

theorem fqA22 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 22)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 22)).2 b)) cb = true := by
  decide +kernel

theorem fqP22a : fqP (nat_lit 22) (nat_lit 0) = true := fqP_all fqA22 (by decide)

theorem fqP22b : fqP (nat_lit 22) (nat_lit 305530) = true := fqP_all fqA22 (by decide)

theorem fqP22c : fqP (nat_lit 22) (nat_lit 5604) = true := fqP_all fqA22 (by decide)

theorem fqP22d : fqP (nat_lit 22) (nat_lit 221549) = true := fqP_all fqA22 (by decide)

theorem fqP22e : fqP (nat_lit 22) (nat_lit 266275) = true := fqP_all fqA22 (by decide)

theorem fqP22f : fqP (nat_lit 22) (nat_lit 186844) = true := fqP_all fqA22 (by decide)

end CFSG.KD.Fi24KPerm.Ck

end
