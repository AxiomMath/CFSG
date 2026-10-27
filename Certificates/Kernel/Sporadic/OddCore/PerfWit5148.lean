module

public import Certificates.Kernel.Sporadic.OddCore.PerfWit5148K
public import Certificates.Kernel.Sporadic.OddCore.PerfWitGlue
public import Certificates.Kernel.Sporadic.OddCore.MNF
public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.Sporadic.SmallOddCore.J2Data

public section

namespace CertificateChecks.KernelSpor.PerfWit5148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.PerfWitK
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45
open CertificateChecks.KernelSpor.OddCore

theorem j3 : (j3Rows.all fun r => r.centOrder != 1920 || perfWitOK 6156 r.centGens j3PerfWit2A) =
    true := by
  have hb := j3_base
  rw [bAnd_iff, bAnd_iff] at hb
  obtain ⟨hidc, hidk, hc⟩ := hb
  have h := perfWitOK_of (k := 5) (T := fun j => j3CentTbl (10 + j))
    (G := fun j => J3CentP (10 + j)) (GI := fun j => J3CentI (10 + j)) (idK_sound hidk).symm hidc
    (fun j hj => by rw [← tabT_natArr (j3CentTbl (10 + j)), j3CentTbl_eq (by omega)])
    (fun j hj => ⟨((bAnd_iff _ _).1 (allN_spec hc j hj)).1,
      ((bAnd_iff _ _).1 (allN_spec hc j hj)).2, j3_perm (by omega)⟩) j3_perf
  have e : [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14] =
      (List.range 5).map fun j => j3CentTbl (10 + j) := rfl
  simp only [j3Rows, List.all_cons, List.all_nil, Bool.and_true, bne_self_eq_false,
    Bool.false_or, Nat.reduceBNe, Bool.true_or]
  rw [e]
  exact h

theorem mclIn : (mclRows.all fun r => r.centOrder != 40320 ||
    perfWitOK 275 r.centGens mclPerfWitIn) = true := by
  have h := perfWitOK_of (k := 2) (T := fun j => mclCentTbl (5 + j))
    (G := fun j => McLCT.F (5 + j)) (GI := fun j => MNI (5 + j)) MNd.hidA MNd.hidc
    (fun j hj => MNd.tabF (by omega))
    (fun j hj => ⟨MNd.Fc (by omega), MNd.Ic (by omega), MNd.Finv (by omega)⟩) mcl_in
  have e : [mclCentTbl 5, mclCentTbl 6] = (List.range 2).map fun j => mclCentTbl (5 + j) := rfl
  simp only [mclRows, List.all_cons, List.all_nil, Bool.and_true, bne_self_eq_false,
    Bool.false_or, Nat.reduceBNe, Bool.true_or]
  rw [e]
  exact h

theorem mclOut : (mclRows.all fun r => r.centOrder != 7920 ||
    perfWitOK 275 r.centGens mclPerfWitOut) = true := by
  have h := perfWitOK_of (k := 4) (T := fun j => mclCentTbl (18 + j))
    (G := fun j => McLCT.F (18 + j)) (GI := fun j => MNI (18 + j)) MNd.hidA MNd.hidc
    (fun j hj => MNd.tabF (by omega))
    (fun j hj => ⟨MNd.Fc (by omega), MNd.Ic (by omega), MNd.Finv (by omega)⟩) mcl_out
  have e : [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21] =
      (List.range 4).map fun j => mclCentTbl (18 + j) := rfl
  simp only [mclRows, List.all_cons, List.all_nil, Bool.and_true, bne_self_eq_false,
    Bool.false_or, Nat.reduceBNe, Bool.true_or, Bool.true_and]
  rw [e]
  exact h

theorem j2 : (j2Rows.all fun r => r.centOrder != 1920 || perfWitOK 315 r.centGens j2PerfWit2A) =
    true := by
  have hb := j2_base
  rw [bAnd_iff, bAnd_iff] at hb
  obtain ⟨hidc, hidk, hc⟩ := hb
  have h := perfWitOK_of (k := 4) (T := fun j => j2CentTbl (32 + j))
    (G := fun j => J2CentT.F (32 + j)) (GI := fun j => J2CentI (32 + j)) (idK_sound hidk).symm
    hidc (fun j hj => by rw [← tabT_natArr (j2CentTbl (32 + j)), j2CentTbl_eq (by omega)])
    (fun j hj => ⟨((bAnd_iff _ _).1 (allN_spec hc j hj)).1,
      ((bAnd_iff _ _).1 (allN_spec hc j hj)).2, allN_spec j2_perms (32 + j) (by omega)⟩) j2_perf
  have e : [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35] =
      (List.range 4).map fun j => j2CentTbl (32 + j) := rfl
  simp only [j2Rows, List.all_cons, List.all_nil, Bool.and_true, bne_self_eq_false,
    Bool.false_or, Nat.reduceBNe, Bool.true_or, Bool.true_and]
  rw [e]
  exact h

end CertificateChecks.KernelSpor.PerfWit5148

end
