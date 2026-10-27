module

public import Certificates.Kernel.Sporadic.OddCore.J3SylFourP
public import Certificates.Kernel.Sporadic.OddCore.J3HypSylF
public import Certificates.Kernel.Sporadic.OddCore.SylFourRows

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3SylFourP

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.OddCore

theorem cgP_perm {l : Nat} (hl : l < 5) :
    invEqK 6156 13 (mask 13) (6156 * 13) (cgP l) (cgPI l) = true :=
  j3_perm (k := l + 10) (by omega)

theorem cgP_get {j : Nat} (hj : j < 5) : cgP0[j]! = j3CentTbl (j + 10) := by
  rw [cgP0, getElem!_pos _ j (by simpa using hj)]
  interval_cases j
  all_goals simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

theorem cgP_tabs : TabsOK 6156 13 5 cgP cgP0 := by
  refine ⟨rfl, fun j hj => ⟨?_, (canonK_of_invEqK J3HypSyl.base.1 (cgP_perm hj)).1⟩⟩
  rw [cgP_get hj, tbl_unpack (by omega)]
  rfl

theorem p0_row {i : Nat} (hi : i < 128) : p0Row i = true := by
  rcases Nat.lt_or_ge i 16 with h0 | h0
  · exact slK_spec p0Five0 i (by omega) (by omega) hi
  rcases Nat.lt_or_ge i 32 with h1 | h1
  · exact slK_spec p0Five1 i h0 (by omega) hi
  rcases Nat.lt_or_ge i 48 with h2 | h2
  · exact slK_spec p0Five2 i h1 (by omega) hi
  rcases Nat.lt_or_ge i 64 with h3 | h3
  · exact slK_spec p0Five3 i h2 (by omega) hi
  rcases Nat.lt_or_ge i 80 with h4 | h4
  · exact slK_spec p0Five4 i h3 (by omega) hi
  rcases Nat.lt_or_ge i 96 with h5 | h5
  · exact slK_spec p0Five5 i h4 (by omega) hi
  rcases Nat.lt_or_ge i 112 with h6 | h6
  · exact slK_spec p0Five6 i h5 (by omega) hi
  · exact slK_spec p0Five7 i h6 (by omega) hi

theorem p0_rows : (mulClosureH 6156 sgP0 128).1.all (fun s => !ordTest 6156 4 s ||
    CFSG.EvenSporadicStandard.HypOne.fiveConjOK 6156 6 cgP0 (cgP0.map (invT 6156)) s) = true := by
  rw [J3HypSyl.closure_eq]
  change (Array.ofFn (n := J3HS.cnt) fun i => tabT (unpack 6156 13 (J3HS.T i.val))).all _ = true
  refine sylRows_all (k := 5) (f := 2) (G := cgP) (GI := cgPI) (by norm_num) J3HypSyl.base.1
    (by norm_num) J3HypSyl.hidc cgP_tabs (fun l hl => cgP_perm hl)
    (fun i hi => J3HypSyl.hT (by rw [← J3HypSyl.hcnt]; exact hi)) (fun i hi hc => ?_)
  have hr := p0_row (by rw [← J3HypSyl.hcnt]; exact hi)
  unfold p0Row at hr
  simp only [CFSG.KS.PF.strictB_eqP] at hr
  unfold rowP at hr
  simp only [CFSG.KS.PF.strictB_eqP] at hr
  exact row_imp hr hc

end CertificateChecks.KernelSpor.J3SylFourP

end
