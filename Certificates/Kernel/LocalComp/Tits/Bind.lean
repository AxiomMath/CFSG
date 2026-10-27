module

public import Certificates.Kernel.LocalComp.Tits.Data
public import CFSG.Certificates.Kernel.LocalCompTitsSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Tits

open CFSG.KC.LocalComp.Tits CFSG.SectionRank.Native.Tits

@[expose] def CP : List Nat :=
  [0, 1, 7, 5, 0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 27, 29,
    31, 35, 37, 38, 39, 40, 41, 42, 43, 47, 48, 59, 61, 63, 67, 69, 70, 73, 83, 87, 99, 101, 103,
    219, 347, 475, 477, 479, 987]

theorem kOrbit : orbitK genCols 2048 4000 1755 TP TG TR = true := by quickRfl

theorem kCheck : checkK 1755 TP baseVecs.toList CP = true := by quickRfl

theorem pts_eq : orbitPts = Array.ofFn (n := 1755) (fun i => TP i.val) := by
  rw [orbitPts, show (2 : Nat) ^ 11 = 2048 from rfl]
  exact (orbit_sound kOrbit).1

theorem gens_eq : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val) := by
  rw [genTables, orbitPts, show (2 : Nat) ^ 11 = 2048 from rfl]
  exact (orbit_sound kOrbit).2.1

theorem base_eq : chainBase = (CP.take 4).toArray := (checkPts_sound pts_eq kCheck).1

theorem check_eq : checkPts = CP.toArray := by
  have h := (checkPts_sound pts_eq kCheck).2
  have e : baseVecs.toList.length = 4 := rfl
  change chainBase ++ basisIdx orbitPts = CP.toArray
  rw [base_eq, h, e, List.append_toArray, List.take_append_drop]

end CertificateChecks.KernelLC.Tits
