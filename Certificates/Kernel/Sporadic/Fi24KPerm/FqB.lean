module

public import Certificates.Kernel.Sporadic.Fi24KPerm.FqL

set_option Elab.async false
set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24Sev
  CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem fqA23 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 23)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 23)).2 b)) cb = true := by
  decide +kernel

theorem fqP23a : fqP (nat_lit 23) (nat_lit 0) = true := fqP_all fqA23 (by decide)

theorem fqP23b : fqP (nat_lit 23) (nat_lit 305530) = true := fqP_all fqA23 (by decide)

theorem fqP23c : fqP (nat_lit 23) (nat_lit 5604) = true := fqP_all fqA23 (by decide)

theorem fqP23d : fqP (nat_lit 23) (nat_lit 221549) = true := fqP_all fqA23 (by decide)

theorem fqP23e : fqP (nat_lit 23) (nat_lit 266275) = true := fqP_all fqA23 (by decide)

theorem fqP23f : fqP (nat_lit 23) (nat_lit 186844) = true := fqP_all fqA23 (by decide)

theorem fqA24 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 24)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 24)).2 b)) cb = true := by
  decide +kernel

theorem fqP24a : fqP (nat_lit 24) (nat_lit 0) = true := fqP_all fqA24 (by decide)

theorem fqP24b : fqP (nat_lit 24) (nat_lit 305530) = true := fqP_all fqA24 (by decide)

theorem fqP24c : fqP (nat_lit 24) (nat_lit 5604) = true := fqP_all fqA24 (by decide)

theorem fqP24d : fqP (nat_lit 24) (nat_lit 221549) = true := fqP_all fqA24 (by decide)

theorem fqP24e : fqP (nat_lit 24) (nat_lit 266275) = true := fqP_all fqA24 (by decide)

theorem fqP24f : fqP (nat_lit 24) (nat_lit 186844) = true := fqP_all fqA24 (by decide)

theorem fqA25 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 25)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 25)).2 b)) cb = true := by
  decide +kernel

theorem fqP25a : fqP (nat_lit 25) (nat_lit 0) = true := fqP_all fqA25 (by decide)

theorem fqP25b : fqP (nat_lit 25) (nat_lit 305530) = true := fqP_all fqA25 (by decide)

theorem fqP25c : fqP (nat_lit 25) (nat_lit 5604) = true := fqP_all fqA25 (by decide)

theorem fqP25d : fqP (nat_lit 25) (nat_lit 221549) = true := fqP_all fqA25 (by decide)

theorem fqP25e : fqP (nat_lit 25) (nat_lit 266275) = true := fqP_all fqA25 (by decide)

theorem fqP25f : fqP (nat_lit 25) (nat_lit 186844) = true := fqP_all fqA25 (by decide)

theorem fqA26 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 26)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 26)).2 b)) cb = true := by
  decide +kernel

theorem fqP26a : fqP (nat_lit 26) (nat_lit 0) = true := fqP_all fqA26 (by decide)

theorem fqP26b : fqP (nat_lit 26) (nat_lit 305530) = true := fqP_all fqA26 (by decide)

theorem fqP26c : fqP (nat_lit 26) (nat_lit 5604) = true := fqP_all fqA26 (by decide)

theorem fqP26d : fqP (nat_lit 26) (nat_lit 221549) = true := fqP_all fqA26 (by decide)

theorem fqP26e : fqP (nat_lit 26) (nat_lit 266275) = true := fqP_all fqA26 (by decide)

theorem fqP26f : fqP (nat_lit 26) (nat_lit 186844) = true := fqP_all fqA26 (by decide)

theorem fqA27 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 27)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 27)).2 b)) cb = true := by
  decide +kernel

theorem fqP27a : fqP (nat_lit 27) (nat_lit 0) = true := fqP_all fqA27 (by decide)

theorem fqP27b : fqP (nat_lit 27) (nat_lit 305530) = true := fqP_all fqA27 (by decide)

theorem fqP27c : fqP (nat_lit 27) (nat_lit 5604) = true := fqP_all fqA27 (by decide)

theorem fqP27d : fqP (nat_lit 27) (nat_lit 221549) = true := fqP_all fqA27 (by decide)

theorem fqP27e : fqP (nat_lit 27) (nat_lit 266275) = true := fqP_all fqA27 (by decide)

theorem fqP27f : fqP (nat_lit 27) (nat_lit 186844) = true := fqP_all fqA27 (by decide)

theorem fqA28 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 28)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 28)).2 b)) cb = true := by
  decide +kernel

theorem fqP28a : fqP (nat_lit 28) (nat_lit 0) = true := fqP_all fqA28 (by decide)

theorem fqP28b : fqP (nat_lit 28) (nat_lit 305530) = true := fqP_all fqA28 (by decide)

theorem fqP28c : fqP (nat_lit 28) (nat_lit 5604) = true := fqP_all fqA28 (by decide)

theorem fqP28d : fqP (nat_lit 28) (nat_lit 221549) = true := fqP_all fqA28 (by decide)

theorem fqP28e : fqP (nat_lit 28) (nat_lit 266275) = true := fqP_all fqA28 (by decide)

theorem fqP28f : fqP (nat_lit 28) (nat_lit 186844) = true := fqP_all fqA28 (by decide)

theorem fqA29 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 29)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 29)).2 b)) cb = true := by
  decide +kernel

theorem fqP29a : fqP (nat_lit 29) (nat_lit 0) = true := fqP_all fqA29 (by decide)

theorem fqP29b : fqP (nat_lit 29) (nat_lit 305530) = true := fqP_all fqA29 (by decide)

theorem fqP29c : fqP (nat_lit 29) (nat_lit 5604) = true := fqP_all fqA29 (by decide)

theorem fqP29d : fqP (nat_lit 29) (nat_lit 221549) = true := fqP_all fqA29 (by decide)

theorem fqP29e : fqP (nat_lit 29) (nat_lit 266275) = true := fqP_all fqA29 (by decide)

theorem fqP29f : fqP (nat_lit 29) (nat_lit 186844) = true := fqP_all fqA29 (by decide)

theorem fqA30 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 30)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 30)).2 b)) cb = true := by
  decide +kernel

theorem fqP30a : fqP (nat_lit 30) (nat_lit 0) = true := fqP_all fqA30 (by decide)

theorem fqP30b : fqP (nat_lit 30) (nat_lit 305530) = true := fqP_all fqA30 (by decide)

theorem fqP30c : fqP (nat_lit 30) (nat_lit 5604) = true := fqP_all fqA30 (by decide)

theorem fqP30d : fqP (nat_lit 30) (nat_lit 221549) = true := fqP_all fqA30 (by decide)

theorem fqP30e : fqP (nat_lit 30) (nat_lit 266275) = true := fqP_all fqA30 (by decide)

theorem fqP30f : fqP (nat_lit 30) (nat_lit 186844) = true := fqP_all fqA30 (by decide)

theorem fqA31 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 31)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 31)).2 b)) cb = true := by
  decide +kernel

theorem fqP31a : fqP (nat_lit 31) (nat_lit 0) = true := fqP_all fqA31 (by decide)

theorem fqP31b : fqP (nat_lit 31) (nat_lit 305530) = true := fqP_all fqA31 (by decide)

theorem fqP31c : fqP (nat_lit 31) (nat_lit 5604) = true := fqP_all fqA31 (by decide)

theorem fqP31d : fqP (nat_lit 31) (nat_lit 221549) = true := fqP_all fqA31 (by decide)

theorem fqP31e : fqP (nat_lit 31) (nat_lit 266275) = true := fqP_all fqA31 (by decide)

theorem fqP31f : fqP (nat_lit 31) (nat_lit 186844) = true := fqP_all fqA31 (by decide)

theorem fqA32 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 32)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 32)).2 b)) cb = true := by
  decide +kernel

theorem fqP32a : fqP (nat_lit 32) (nat_lit 0) = true := fqP_all fqA32 (by decide)

theorem fqP32b : fqP (nat_lit 32) (nat_lit 305530) = true := fqP_all fqA32 (by decide)

theorem fqP32c : fqP (nat_lit 32) (nat_lit 5604) = true := fqP_all fqA32 (by decide)

theorem fqP32d : fqP (nat_lit 32) (nat_lit 221549) = true := fqP_all fqA32 (by decide)

theorem fqP32e : fqP (nat_lit 32) (nat_lit 266275) = true := fqP_all fqA32 (by decide)

theorem fqP32f : fqP (nat_lit 32) (nat_lit 186844) = true := fqP_all fqA32 (by decide)

theorem fqA33 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 33)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 33)).2 b)) cb = true := by
  decide +kernel

theorem fqP33a : fqP (nat_lit 33) (nat_lit 0) = true := fqP_all fqA33 (by decide)

theorem fqP33b : fqP (nat_lit 33) (nat_lit 305530) = true := fqP_all fqA33 (by decide)

theorem fqP33c : fqP (nat_lit 33) (nat_lit 5604) = true := fqP_all fqA33 (by decide)

theorem fqP33d : fqP (nat_lit 33) (nat_lit 221549) = true := fqP_all fqA33 (by decide)

theorem fqP33e : fqP (nat_lit 33) (nat_lit 266275) = true := fqP_all fqA33 (by decide)

theorem fqP33f : fqP (nat_lit 33) (nat_lit 186844) = true := fqP_all fqA33 (by decide)

theorem fqA34 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 34)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 34)).2 b)) cb = true := by
  decide +kernel

theorem fqP34a : fqP (nat_lit 34) (nat_lit 0) = true := fqP_all fqA34 (by decide)

theorem fqP34b : fqP (nat_lit 34) (nat_lit 305530) = true := fqP_all fqA34 (by decide)

theorem fqP34c : fqP (nat_lit 34) (nat_lit 5604) = true := fqP_all fqA34 (by decide)

theorem fqP34d : fqP (nat_lit 34) (nat_lit 221549) = true := fqP_all fqA34 (by decide)

theorem fqP34e : fqP (nat_lit 34) (nat_lit 266275) = true := fqP_all fqA34 (by decide)

theorem fqP34f : fqP (nat_lit 34) (nat_lit 186844) = true := fqP_all fqA34 (by decide)

theorem fqA35 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 35)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 35)).2 b)) cb = true := by
  decide +kernel

theorem fqP35a : fqP (nat_lit 35) (nat_lit 0) = true := fqP_all fqA35 (by decide)

theorem fqP35b : fqP (nat_lit 35) (nat_lit 305530) = true := fqP_all fqA35 (by decide)

theorem fqP35c : fqP (nat_lit 35) (nat_lit 5604) = true := fqP_all fqA35 (by decide)

theorem fqP35d : fqP (nat_lit 35) (nat_lit 221549) = true := fqP_all fqA35 (by decide)

theorem fqP35e : fqP (nat_lit 35) (nat_lit 266275) = true := fqP_all fqA35 (by decide)

theorem fqP35f : fqP (nat_lit 35) (nat_lit 186844) = true := fqP_all fqA35 (by decide)

theorem fqA36 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 36)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 36)).2 b)) cb = true := by
  decide +kernel

theorem fqP36a : fqP (nat_lit 36) (nat_lit 0) = true := fqP_all fqA36 (by decide)

theorem fqP36b : fqP (nat_lit 36) (nat_lit 305530) = true := fqP_all fqA36 (by decide)

theorem fqP36c : fqP (nat_lit 36) (nat_lit 5604) = true := fqP_all fqA36 (by decide)

theorem fqP36d : fqP (nat_lit 36) (nat_lit 221549) = true := fqP_all fqA36 (by decide)

theorem fqP36e : fqP (nat_lit 36) (nat_lit 266275) = true := fqP_all fqA36 (by decide)

theorem fqP36f : fqP (nat_lit 36) (nat_lit 186844) = true := fqP_all fqA36 (by decide)

theorem fqA37 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 37)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 37)).2 b)) cb = true := by
  decide +kernel

theorem fqP37a : fqP (nat_lit 37) (nat_lit 0) = true := fqP_all fqA37 (by decide)

theorem fqP37b : fqP (nat_lit 37) (nat_lit 305530) = true := fqP_all fqA37 (by decide)

theorem fqP37c : fqP (nat_lit 37) (nat_lit 5604) = true := fqP_all fqA37 (by decide)

theorem fqP37d : fqP (nat_lit 37) (nat_lit 221549) = true := fqP_all fqA37 (by decide)

theorem fqP37e : fqP (nat_lit 37) (nat_lit 266275) = true := fqP_all fqA37 (by decide)

theorem fqP37f : fqP (nat_lit 37) (nat_lit 186844) = true := fqP_all fqA37 (by decide)

theorem fqA38 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 38)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 38)).2 b)) cb = true := by
  decide +kernel

theorem fqP38a : fqP (nat_lit 38) (nat_lit 0) = true := fqP_all fqA38 (by decide)

theorem fqP38b : fqP (nat_lit 38) (nat_lit 305530) = true := fqP_all fqA38 (by decide)

theorem fqP38c : fqP (nat_lit 38) (nat_lit 5604) = true := fqP_all fqA38 (by decide)

theorem fqP38d : fqP (nat_lit 38) (nat_lit 221549) = true := fqP_all fqA38 (by decide)

theorem fqP38e : fqP (nat_lit 38) (nat_lit 266275) = true := fqP_all fqA38 (by decide)

theorem fqP38f : fqP (nat_lit 38) (nat_lit 186844) = true := fqP_all fqA38 (by decide)

theorem fqA39 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 39)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 39)).2 b)) cb = true := by
  decide +kernel

theorem fqP39a : fqP (nat_lit 39) (nat_lit 0) = true := fqP_all fqA39 (by decide)

theorem fqP39b : fqP (nat_lit 39) (nat_lit 305530) = true := fqP_all fqA39 (by decide)

theorem fqP39c : fqP (nat_lit 39) (nat_lit 5604) = true := fqP_all fqA39 (by decide)

theorem fqP39d : fqP (nat_lit 39) (nat_lit 221549) = true := fqP_all fqA39 (by decide)

theorem fqP39e : fqP (nat_lit 39) (nat_lit 266275) = true := fqP_all fqA39 (by decide)

theorem fqP39f : fqP (nat_lit 39) (nat_lit 186844) = true := fqP_all fqA39 (by decide)

theorem fqA40 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 40)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 40)).2 b)) cb = true := by
  decide +kernel

theorem fqP40a : fqP (nat_lit 40) (nat_lit 0) = true := fqP_all fqA40 (by decide)

theorem fqP40b : fqP (nat_lit 40) (nat_lit 305530) = true := fqP_all fqA40 (by decide)

theorem fqP40c : fqP (nat_lit 40) (nat_lit 5604) = true := fqP_all fqA40 (by decide)

theorem fqP40d : fqP (nat_lit 40) (nat_lit 221549) = true := fqP_all fqA40 (by decide)

theorem fqP40e : fqP (nat_lit 40) (nat_lit 266275) = true := fqP_all fqA40 (by decide)

theorem fqP40f : fqP (nat_lit 40) (nat_lit 186844) = true := fqP_all fqA40 (by decide)

theorem fqA41 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 41)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 41)).2 b)) cb = true := by
  decide +kernel

theorem fqP41a : fqP (nat_lit 41) (nat_lit 0) = true := fqP_all fqA41 (by decide)

theorem fqP41b : fqP (nat_lit 41) (nat_lit 305530) = true := fqP_all fqA41 (by decide)

theorem fqP41c : fqP (nat_lit 41) (nat_lit 5604) = true := fqP_all fqA41 (by decide)

theorem fqP41d : fqP (nat_lit 41) (nat_lit 221549) = true := fqP_all fqA41 (by decide)

theorem fqP41e : fqP (nat_lit 41) (nat_lit 266275) = true := fqP_all fqA41 (by decide)

theorem fqP41f : fqP (nat_lit 41) (nat_lit 186844) = true := fqP_all fqA41 (by decide)

theorem fqA42 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 42)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 42)).2 b)) cb = true := by
  decide +kernel

theorem fqP42a : fqP (nat_lit 42) (nat_lit 0) = true := fqP_all fqA42 (by decide)

theorem fqP42b : fqP (nat_lit 42) (nat_lit 305530) = true := fqP_all fqA42 (by decide)

theorem fqP42c : fqP (nat_lit 42) (nat_lit 5604) = true := fqP_all fqA42 (by decide)

theorem fqP42d : fqP (nat_lit 42) (nat_lit 221549) = true := fqP_all fqA42 (by decide)

theorem fqP42e : fqP (nat_lit 42) (nat_lit 266275) = true := fqP_all fqA42 (by decide)

theorem fqP42f : fqP (nat_lit 42) (nat_lit 186844) = true := fqP_all fqA42 (by decide)

theorem fqA43 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 43)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 43)).2 b)) cb = true := by
  decide +kernel

theorem fqP43a : fqP (nat_lit 43) (nat_lit 0) = true := fqP_all fqA43 (by decide)

theorem fqP43b : fqP (nat_lit 43) (nat_lit 305530) = true := fqP_all fqA43 (by decide)

theorem fqP43c : fqP (nat_lit 43) (nat_lit 5604) = true := fqP_all fqA43 (by decide)

theorem fqP43d : fqP (nat_lit 43) (nat_lit 221549) = true := fqP_all fqA43 (by decide)

theorem fqP43e : fqP (nat_lit 43) (nat_lit 266275) = true := fqP_all fqA43 (by decide)

theorem fqP43f : fqP (nat_lit 43) (nat_lit 186844) = true := fqP_all fqA43 (by decide)

theorem fqA44 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 44)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 44)).2 b)) cb = true := by
  decide +kernel

theorem fqP44a : fqP (nat_lit 44) (nat_lit 0) = true := fqP_all fqA44 (by decide)

theorem fqP44b : fqP (nat_lit 44) (nat_lit 305530) = true := fqP_all fqA44 (by decide)

theorem fqP44c : fqP (nat_lit 44) (nat_lit 5604) = true := fqP_all fqA44 (by decide)

theorem fqP44d : fqP (nat_lit 44) (nat_lit 221549) = true := fqP_all fqA44 (by decide)

theorem fqP44e : fqP (nat_lit 44) (nat_lit 266275) = true := fqP_all fqA44 (by decide)

theorem fqP44f : fqP (nat_lit 44) (nat_lit 186844) = true := fqP_all fqA44 (by decide)

theorem fqA45 : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 45)).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq (nat_lit 45)).2 b)) cb = true := by
  decide +kernel

theorem fqP45a : fqP (nat_lit 45) (nat_lit 0) = true := fqP_all fqA45 (by decide)

theorem fqP45b : fqP (nat_lit 45) (nat_lit 305530) = true := fqP_all fqA45 (by decide)

theorem fqP45c : fqP (nat_lit 45) (nat_lit 5604) = true := fqP_all fqA45 (by decide)

theorem fqP45d : fqP (nat_lit 45) (nat_lit 221549) = true := fqP_all fqA45 (by decide)

theorem fqP45e : fqP (nat_lit 45) (nat_lit 266275) = true := fqP_all fqA45 (by decide)

theorem fqP45f : fqP (nat_lit 45) (nat_lit 186844) = true := fqP_all fqA45 (by decide)

end CFSG.KD.Fi24KPerm.Ck

end
