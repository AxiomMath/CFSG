module

public import Certificates.Kernel.M23Three.Chain
public import Certificates.Data.Kernel.PermCent.Seal
import CFSG.Certificates.Kernel.Common.NatVal

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelM23Three

open CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkCV

#kc_natval sa0 := ((strongV QF).getD 0 (oneV 23)).1.1
#kc_natval sb0 := ((strongV QF).getD 0 (oneV 23)).1.2
#kc_natval sa1 := ((strongV QF).getD 1 (oneV 23)).1.1
#kc_natval sb1 := ((strongV QF).getD 1 (oneV 23)).1.2
#kc_natval sa2 := ((strongV QF).getD 2 (oneV 23)).1.1
#kc_natval sb2 := ((strongV QF).getD 2 (oneV 23)).1.2
#kc_natval sa3 := ((strongV QF).getD 3 (oneV 23)).1.1
#kc_natval sb3 := ((strongV QF).getD 3 (oneV 23)).1.2
#kc_natval sa4 := ((strongV QF).getD 4 (oneV 23)).1.1
#kc_natval sb4 := ((strongV QF).getD 4 (oneV 23)).1.2
#kc_natval sa5 := ((strongV QF).getD 5 (oneV 23)).1.1
#kc_natval sb5 := ((strongV QF).getD 5 (oneV 23)).1.2
#kc_natval sa6 := ((strongV QF).getD 6 (oneV 23)).1.1
#kc_natval sb6 := ((strongV QF).getD 6 (oneV 23)).1.2
#kc_natval sa7 := ((strongV QF).getD 7 (oneV 23)).1.1
#kc_natval sb7 := ((strongV QF).getD 7 (oneV 23)).1.2
#kc_natval sa8 := ((strongV QF).getD 8 (oneV 23)).1.1
#kc_natval sb8 := ((strongV QF).getD 8 (oneV 23)).1.2
#kc_natval sa9 := ((strongV QF).getD 9 (oneV 23)).1.1
#kc_natval sb9 := ((strongV QF).getD 9 (oneV 23)).1.2
#kc_natval sa10 := ((strongV QF).getD 10 (oneV 23)).1.1
#kc_natval sb10 := ((strongV QF).getD 10 (oneV 23)).1.2
#kc_natval sa11 := ((strongV QF).getD 11 (oneV 23)).1.1
#kc_natval sb11 := ((strongV QF).getD 11 (oneV 23)).1.2
#kc_natval sa12 := ((strongV QF).getD 12 (oneV 23)).1.1
#kc_natval sb12 := ((strongV QF).getD 12 (oneV 23)).1.2
#kc_natval sa13 := ((strongV QF).getD 13 (oneV 23)).1.1
#kc_natval sb13 := ((strongV QF).getD 13 (oneV 23)).1.2
#kc_natval sa14 := ((strongV QF).getD 14 (oneV 23)).1.1
#kc_natval sb14 := ((strongV QF).getD 14 (oneV 23)).1.2
#kc_natval sa15 := ((strongV QF).getD 15 (oneV 23)).1.1
#kc_natval sb15 := ((strongV QF).getD 15 (oneV 23)).1.2
#kc_natval sa16 := ((strongV QF).getD 16 (oneV 23)).1.1
#kc_natval sb16 := ((strongV QF).getD 16 (oneV 23)).1.2
#kc_natval sa17 := ((strongV QF).getD 17 (oneV 23)).1.1
#kc_natval sb17 := ((strongV QF).getD 17 (oneV 23)).1.2
#kc_natval sa18 := ((strongV QF).getD 18 (oneV 23)).1.1
#kc_natval sb18 := ((strongV QF).getD 18 (oneV 23)).1.2
#kc_natval sa19 := ((strongV QF).getD 19 (oneV 23)).1.1
#kc_natval sb19 := ((strongV QF).getD 19 (oneV 23)).1.2
#kc_natval sa20 := ((strongV QF).getD 20 (oneV 23)).1.1
#kc_natval sb20 := ((strongV QF).getD 20 (oneV 23)).1.2
#kc_natval sa21 := ((strongV QF).getD 21 (oneV 23)).1.1
#kc_natval sb21 := ((strongV QF).getD 21 (oneV 23)).1.2
#kc_natval sa22 := ((strongV QF).getD 22 (oneV 23)).1.1
#kc_natval sb22 := ((strongV QF).getD 22 (oneV 23)).1.2
#kc_natval sa23 := ((strongV QF).getD 23 (oneV 23)).1.1
#kc_natval sb23 := ((strongV QF).getD 23 (oneV 23)).1.2
#kc_natval sa24 := ((strongV QF).getD 24 (oneV 23)).1.1
#kc_natval sb24 := ((strongV QF).getD 24 (oneV 23)).1.2
#kc_natval sa25 := ((strongV QF).getD 25 (oneV 23)).1.1
#kc_natval sb25 := ((strongV QF).getD 25 (oneV 23)).1.2
#kc_natval sa26 := ((strongV QF).getD 26 (oneV 23)).1.1
#kc_natval sb26 := ((strongV QF).getD 26 (oneV 23)).1.2

@[expose] noncomputable def strongL : List (Nat × Nat) :=
  [(sa0, sb0), (sa1, sb1), (sa2, sb2), (sa3, sb3), (sa4, sb4), (sa5, sb5), (sa6, sb6),
    (sa7, sb7), (sa8, sb8), (sa9, sb9), (sa10, sb10), (sa11, sb11), (sa12, sb12), (sa13, sb13),
    (sa14, sb14), (sa15, sb15), (sa16, sb16), (sa17, sb17), (sa18, sb18), (sa19, sb19),
    (sa20, sb20), (sa21, sb21), (sa22, sb22), (sa23, sb23), (sa24, sb24), (sa25, sb25),
    (sa26, sb26)]

theorem strongL_length : strongL.length = 27 := rfl

theorem strongL_ok : (List.range 27).all (fun k => Seal.codeAt (strongV QF) strongL k) = true := by
  decide +kernel

theorem strongV_eqL : strongV QF = strongL.map (Seal.mkVP 23) :=
  Seal.eq_map_mkVP_of_getD (by decide +kernel) fun k hk =>
    List.all_eq_true.1 strongL_ok k (List.mem_range.2 (strongL_length ▸ hk))

theorem kQFh : Seal.schHead (strongL.map (Seal.mkVP 23)) QF.base = true := by decide +kernel

theorem kQF0 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨0, by decide⟩ = true := by
  decide +kernel

theorem kQF1 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨1, by decide⟩ = true := by
  decide +kernel

theorem kQF2 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨2, by decide⟩ = true := by
  decide +kernel

theorem kQF3 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨3, by decide⟩ = true := by
  decide +kernel

theorem kQF4 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨4, by decide⟩ = true := by
  decide +kernel

theorem kQF5 : Seal.schLev (strongL.map (Seal.mkVP 23)) QF.base ⟨5, by decide⟩ = true := by
  decide +kernel

theorem kQF : schP QF = true := by
  unfold schP
  rw [strongV_eqL]
  refine Seal.schV_of kQFh fun ⟨i, hi⟩ => ?_
  match i, hi with
  | 0, _ => exact kQF0
  | 1, _ => exact kQF1
  | 2, _ => exact kQF2
  | 3, _ => exact kQF3
  | 4, _ => exact kQF4
  | 5, _ => exact kQF5
  | k + 6, h => exact absurd h (by rw [show QF.baseCount = 6 from rfl]; omega)

theorem kOrbits : ((List.finRange QF.baseCount).map fun i =>
    (levelV (strongV QF) QF.base i).entries.length) = [23, 22, 21, 20, 16, 3] := by
  decide +kernel

theorem kRel : relC = true := by decide +kernel

theorem kFix : fixC = true := by decide +kernel

end CertificateChecks.KernelM23Three
