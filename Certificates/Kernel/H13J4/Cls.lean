
module

public import Certificates.Kernel.SporSch.J4S.Orbits
public import CFSG.Certificates.Kernel.H13J4.ClsSound
meta import Certificates.Kernel.H13J4.ClsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_tree CertificateChecks.KernelH13.J4C2T CertificateChecks.KernelH13.J4ClsData.e2E 11
#kss_vec CertificateChecks.KernelH13.J4C2PAR CertificateChecks.KernelH13.J4ClsData.e2P
#kss_vec CertificateChecks.KernelH13.J4C2GEN CertificateChecks.KernelH13.J4ClsData.e2G
#kss_vec CertificateChecks.KernelH13.J4C2NX CertificateChecks.KernelH13.J4ClsData.e2N
#kss_sort CertificateChecks.KernelH13.J4C2 CertificateChecks.KernelH13.J4ClsData.e2E 11
#kss_tree CertificateChecks.KernelH13.J4C3T CertificateChecks.KernelH13.J4ClsData.e3E 11
#kss_vec CertificateChecks.KernelH13.J4C3PAR CertificateChecks.KernelH13.J4ClsData.e3P
#kss_vec CertificateChecks.KernelH13.J4C3GEN CertificateChecks.KernelH13.J4ClsData.e3G
#kss_vec CertificateChecks.KernelH13.J4C3NX CertificateChecks.KernelH13.J4ClsData.e3N
#kss_sort CertificateChecks.KernelH13.J4C3 CertificateChecks.KernelH13.J4ClsData.e3E 11

namespace CertificateChecks.KernelH13.J4Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KS.H13J4
open CFSG.Sporadic.J4Schreier CFSG.Quasithin.H13.J4
open CertificateChecks.KernelH13 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Orbits

@[expose] noncomputable def f2 : Nat → Bool := stepAt J4XYG J4XYI J4C2T J4C2PAR J4C2GEN J4C2NX 2 11385
@[expose] noncomputable def f3 : Nat → Bool := stepAt J4XYG J4XYI J4C3T J4C3PAR J4C3GEN J4C3NX 2 31878

end CertificateChecks.KernelH13.J4Cls

#kss_slices CertificateChecks.KernelH13.J4C2S CertificateChecks.KernelH13.J4Cls.f2 1024 12
#kss_slices CertificateChecks.KernelH13.J4C3S CertificateChecks.KernelH13.J4Cls.f3 1024 32

namespace CertificateChecks.KernelH13.J4Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KS.H13J4
open CFSG.Sporadic.J4Schreier CFSG.Quasithin.H13.J4
open CertificateChecks.KernelH13 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Orbits

theorem r2 : bindWK 11 11 m2Cols.toList (J4C2T 0) = true := by quickRfl
theorem r3 : Nat.beq (J4C3T 0) (J4XYG 0) = true := by quickRfl
theorem d2 : distinctK J4C2T J4C2.SO J4C2.SOI 11385 = true := by quickRfl
theorem d3 : distinctK J4C3T J4C3.SO J4C3.SOI 31878 = true := by quickRfl

theorem gens_bind : ∀ g < 2, (xyPairs[g]!).1 = unpack11 (J4XYG g) ∧
    (xyPairs[g]!).2 = unpack11 (J4XYI g) := by
  intro g hg
  rw [← xy_bind.2 g hg, ← xyi_bind.2 g hg]
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem cls2_facts : ClsFacts xyPairs m2Cols 11385 :=
  clsFacts_of rfl (fun g hg => (gens_bind g hg).1) (fun g hg => (gens_bind g hg).2) (bindW_sound r2)
    d2 (step_of_slices (by norm_num) J4C2S.all)

theorem cls3_facts : ClsFacts xyPairs xColumns 31878 := by
  have e : xColumns = unpack11 (J4C3T 0) := by
    rw [Nat.eq_of_beq_eq_true r3, ← xy_bind.2 0 (by norm_num)]
    rfl
  exact clsFacts_of rfl (fun g hg => (gens_bind g hg).1) (fun g hg => (gens_bind g hg).2) e
    d3 (step_of_slices (by norm_num) J4C3S.all)

end CertificateChecks.KernelH13.J4Cls

end
