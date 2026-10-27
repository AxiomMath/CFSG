module

public import Certificates.Data.Seitz77Sec27SmallJ2
public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSeitz77.J2U0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.HarrisLit.EndB
open CertificateChecks.KernelJ2Cover

@[expose] noncomputable def gS (l : Nat) : Nat := C2B.S (l - 1)

@[expose] noncomputable def U : Nat := wfoldK 315 9 (mask 9) gS [2, 2, 2] (pidn 315 9)

theorem idOK : CFSG.KS.Prim.idK 315 9 (mask 9) = true := by quickRfl

theorem hidc : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := by quickRfl

theorem c0 : canonK 315 9 (mask 9) (315 * 9) (C2B.S 0) = true := by quickRfl

theorem c1 : canonK 315 9 (mask 9) (315 * 9) (C2B.S 1) = true := by quickRfl

theorem cA : canonK 315 9 (mask 9) (315 * 9) (PA.S 0) = true := by quickRfl

theorem p0 : invEqK 315 9 (mask 9) (315 * 9) (C2B.S 0) (C2B.SI 0) = true :=
  allN_spec c2B_perm 0 (by norm_num)

theorem p1 : invEqK 315 9 (mask 9) (315 * 9) (C2B.S 1) (C2B.SI 1) = true :=
  allN_spec c2B_perm 1 (by norm_num)

theorem pU : invEqK 315 9 (mask 9) (315 * 9) U U = true := by quickRfl

theorem arrTable_unpack (X : Nat) : arrTable 315 (unpack 315 9 X) = tabT (unpack 315 9 X) := by
  apply Array.ext (by simp [arrTable, tabT, unpack])
  intro i h1 h2
  simp [arrTable, tabT, unpack]

theorem gens_eq :
    c2BGens = [tabT (unpack 315 9 (C2B.S 0)), tabT (unpack 315 9 (C2B.S 1))] := by
  unfold c2BGens
  rw [c2B_binds.2.2.2.2.1 0 (by norm_num), c2B_binds.2.2.2.2.1 1 (by norm_num), arrTable_unpack,
    arrTable_unpack]

theorem hid : idT 315 = tabT (unpack 315 9 (pidn 315 9)) := by
  rw [idT_tabT, idK_sound idOK]

theorem u_eq : Certificates.Seitz77Sec27.j2U0 = tabT (unpack 315 9 U) ∧
    canonK 315 9 (mask 9) (315 * 9) U = true := by
  unfold Certificates.Seitz77Sec27.j2U0 U
  rw [gens_eq]
  refine wordTbl_unpack hid hidc fun l hl => ?_
  have hl2 : l = 2 := by simpa using hl
  subst hl2
  exact ⟨by simp [gS], c1⟩

theorem invoOK_eq (P : Table) :
    CFSG.Sporadic.Th.Native.invoOK 315 P = tblEq 315 (compT 315 P P) (idT 315) := by
  unfold CFSG.Sporadic.Th.Native.invoOK tblEq
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have h1 : ap (compT 315 P P) i = ap P (ap P i) := by
    unfold ap compT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have h2 : ap (idT 315) i = i := by
    unfold ap idT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]

theorem j2U0Check_true : Certificates.Seitz77Sec27.j2U0Check = true := by
  obtain ⟨eU, cU⟩ := u_eq
  have ha : arrTable 315 autStrong[0]! = tabT (unpack 315 9 (PA.S 0)) := by
    rw [binds.2.2.2.2.1 0 (by norm_num), arrTable_unpack]
  unfold Certificates.Seitz77Sec27.j2U0Check
  rw [gens_eq, eU, ha]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  unfold CFSG.Sporadic.SmallOddCore.involOK
  rw [permOK_unpack c0 p0, permOK_unpack c1 p1, permOK_unpack cU pU, invoOK_eq,
    compT_unpack cU cU, hid, tblEq_unpack (canonK_pcomp cU cU) hidc, tblEq_unpack cU hidc,
    commTT_unpack cU c0, commTT_unpack cU c1, tblEq_unpack cU cA]
  quickRfl

end CertificateChecks.KernelSeitz77.J2U0K

end
