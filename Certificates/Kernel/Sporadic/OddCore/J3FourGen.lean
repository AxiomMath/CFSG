module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.GH74.Uniqueness.SU.KI1r4F61J3Check
public import CFSG.Sporadic.SmallOddCore.J3Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.GH74.Uniqueness.SU.K.R4

@[expose] noncomputable def fourK : Bool :=
  bAnd(canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13), bAnd(idK 6156 13 (mask 13),
  bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 22),
  bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 23),
  bAnd(Nat.beq (pcomp 6156 13 (mask 13) (J3CentP 22) (J3CentP 22)) (pidn 6156 13),
  bAnd(bIf(Nat.beq (J3CentP 22) (pidn 6156 13), false, true),
  bAnd(Nat.beq (pcomp 6156 13 (mask 13) (J3CentP 23) (J3CentP 23)) (pidn 6156 13),
  bAnd(bIf(Nat.beq (J3CentP 23) (pidn 6156 13), false, true),
  bAnd(Nat.beq (pcomp 6156 13 (mask 13) (J3CentP 22) (J3CentP 23))
    (pcomp 6156 13 (mask 13) (J3CentP 23) (J3CentP 22)),
  bIf(Nat.beq (J3CentP 22) (J3CentP 23), false, true))))))))))

theorem four_ok : fourK = true := by
  quickRfl

theorem four_neg : bIf(Nat.beq (J3CentP 22) (J3CentP 22), false, true) = false ∧
    Nat.beq (pcomp 6156 13 (mask 13) (J3CentP 25) (J3CentP 25)) (pidn 6156 13) = false := by
  decide +kernel

theorem tbl_unpack {k : Nat} (hk : k < 31) : j3CentTbl k = tabT (unpack 6156 13 (J3CentP k)) := by
  rw [← tabT_natArr (j3CentTbl k), j3CentTbl_eq hk]

theorem j3_fourGen :
    (j3Rows.all fun r => r.outer == false || fourGenOK 6156 r.centGens 0 1) = true := by
  have h := four_ok
  unfold fourK at h
  simp only [bAnd_iff] at h
  obtain ⟨hidc, hidk, h22, h23, a1, a2, a3, a4, a5, a6⟩ := h
  have hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
    rw [idT_tabT, idK_sound hidk]
  have hp : (List.range 31).all (fun k => permOK 6156 (j3CentTbl k)) = true := j3_permOK_all
  rw [List.all_eq_true] at hp
  have p22 := hp 22 (by simp)
  have p23 := hp 23 (by simp)
  have p24 := hp 24 (by simp)
  simp only [j3Rows, List.all_cons, List.all_nil, beq_self_eq_true, Bool.true_or, Bool.true_and,
    Bool.and_true, Bool.false_or]
  unfold fourGenOK
  simp only [List.length_cons, List.length_nil, List.all_cons, List.all_nil, p22, p23, p24,
    List.getElem!_cons_zero, List.getElem!_cons_succ, Bool.and_true, Bool.true_and]
  rw [tbl_unpack (k := 22) (by norm_num), tbl_unpack (k := 23) (by norm_num),
    involOK_unpack' (by norm_num) hid hidc h22, involOK_unpack' (by norm_num) hid hidc h23,
    commTT_unpack h22 h23, tblEq_unpack h22 h23, a1, a2, a3, a4, a5]
  revert a6
  cases (J3CentP 22).beq (J3CentP 23) <;> decide

end CertificateChecks.KernelSpor.OddCore

end
