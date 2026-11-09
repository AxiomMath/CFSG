
module

public import Certificates.Kernel.SporSch.J4S.Orbits
public import CFSG.Certificates.Kernel.H13J4.ClsSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4ClsLI "Certificates/Kernel/H13J4/data/li.bin" 2816 5632 15753500993349309669
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4ClsR "Certificates/Kernel/H13J4/data/r.bin" 167 334 2401062123488030560
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C2TD "Certificates/Kernel/H13J4/data/c2t.bin" 4096 182160 14519077054682725246
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C2GEND "Certificates/Kernel/H13J4/data/c2g.bin" 4096 22770 5306723475202971925
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C2NXD "Certificates/Kernel/H13J4/data/c2n.bin" 4096 45540 2743674412648113721
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C2.SOD "Certificates/Kernel/H13J4/data/c2so.bin" 4096 22770 11301073746338519888
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C2.SOID "Certificates/Kernel/H13J4/data/c2soi.bin" 4096 22770 2357370846652505180
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C3TD "Certificates/Kernel/H13J4/data/c3t.bin" 4096 510048 13211230754997553297
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C3GEND "Certificates/Kernel/H13J4/data/c3g.bin" 4096 63756 9476654140745450917
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C3NXD "Certificates/Kernel/H13J4/data/c3n.bin" 4096 127512 8613107596968989110
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C3.SOD "Certificates/Kernel/H13J4/data/c3so.bin" 4096 63756 4809012554180795772
#kc_repo #kc_ktreeT CertificateChecks.KernelH13 J4C3.SOID "Certificates/Kernel/H13J4/data/c3soi.bin" 4096 63756 16560831044758029046

namespace CertificateChecks.KernelH13

@[expose] noncomputable def J4ClsEnt16 (D : Nat → Nat) (i : Nat) : Nat :=
  fld(D (Nat.shiftRight i (nat_lit 8)), Nat.mul (nat_lit 128) (Nat.land i (nat_lit 255)),
    nat_lit 340282366920938463463374607431768211455)

@[expose] noncomputable def J4ClsEnt2 (D : Nat → Nat) (i : Nat) : Nat :=
  fld(D (Nat.shiftRight i (nat_lit 11)), Nat.mul (nat_lit 16) (Nat.land i (nat_lit 2047)),
    nat_lit 65535)

@[expose] noncomputable def J4C2T : Nat → Nat := J4ClsEnt16 J4C2TD
@[expose] noncomputable def J4C2GEN : Nat → Nat := J4ClsEnt2 J4C2GEND
@[expose] noncomputable def J4C2NX : Nat → Nat := J4ClsEnt2 J4C2NXD
@[expose] noncomputable def J4C2.SO : Nat → Nat := J4ClsEnt2 J4C2.SOD
@[expose] noncomputable def J4C2.SOI : Nat → Nat := J4ClsEnt2 J4C2.SOID
@[expose] noncomputable def J4C3T : Nat → Nat := J4ClsEnt16 J4C3TD
@[expose] noncomputable def J4C3GEN : Nat → Nat := J4ClsEnt2 J4C3GEND
@[expose] noncomputable def J4C3NX : Nat → Nat := J4ClsEnt2 J4C3NXD
@[expose] noncomputable def J4C3.SO : Nat → Nat := J4ClsEnt2 J4C3.SOD
@[expose] noncomputable def J4C3.SOI : Nat → Nat := J4ClsEnt2 J4C3.SOID

end CertificateChecks.KernelH13

namespace CertificateChecks.KernelH13.J4Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KS.H13J4
open CFSG.Sporadic.J4Schreier CFSG.Quasithin.H13.J4
open CertificateChecks.KernelH13 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Orbits

@[expose] noncomputable def f2 : Nat → Bool := stepAt J4ClsLI J4ClsR J4C2T J4C2GEN J4C2NX 2 11385
@[expose] noncomputable def f3 : Nat → Bool := stepAt J4ClsLI J4ClsR J4C3T J4C3GEN J4C3NX 2 31878

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
theorem inv0 : Nat.beq (compK (J4XYG 0) (J4XYI 0)) pidK = true := by quickRfl
theorem inv1 : Nat.beq (compK (J4XYG 1) (J4XYI 1)) pidK = true := by quickRfl
theorem tab0 : appTabOK (J4XYI 0) (J4ClsLI 0) = true := by quickRfl
theorem tab1 : appTabOK (J4XYI 1) (J4ClsLI 1) = true := by quickRfl
theorem row0 : rowOK (J4XYG 0) (J4ClsR 0) = true := by quickRfl
theorem row1 : rowOK (J4XYG 1) (J4ClsR 1) = true := by quickRfl

theorem gens_inv : ∀ g < 2, Nat.beq (compK (J4XYG g) (J4XYI g)) pidK = true := by
  intro g hg
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact inv0
  · exact inv1

theorem gens_tab : ∀ g < 2, appTabOK (J4XYI g) (J4ClsLI g) = true := by
  intro g hg
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact tab0
  · exact tab1

theorem gens_row : ∀ g < 2, rowOK (J4XYG g) (J4ClsR g) = true := by
  intro g hg
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact row0
  · exact row1

theorem gens_bind : ∀ g < 2, (xyPairs[g]!).1 = unpack11 (J4XYG g) ∧
    (xyPairs[g]!).2 = unpack11 (J4XYI g) := by
  intro g hg
  rw [← xy_bind.2 g hg, ← xyi_bind.2 g hg]
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem cls2_facts : ClsFacts xyPairs m2Cols 11385 :=
  clsFacts_of rfl (fun g hg => (gens_bind g hg).1) (fun g hg => (gens_bind g hg).2) gens_inv
    gens_tab gens_row (bindW_sound r2) d2 (step_of_slices (by norm_num) J4C2S.all)

theorem cls3_facts : ClsFacts xyPairs xColumns 31878 := by
  have e : xColumns = unpack11 (J4C3T 0) := by
    rw [Nat.eq_of_beq_eq_true r3, ← xy_bind.2 0 (by norm_num)]
    rfl
  exact clsFacts_of rfl (fun g hg => (gens_bind g hg).1) (fun g hg => (gens_bind g hg).2) gens_inv
    gens_tab gens_row e d3 (step_of_slices (by norm_num) J4C3S.all)

end CertificateChecks.KernelH13.J4Cls

end
