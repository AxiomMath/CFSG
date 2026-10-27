module

public import Certificates.Kernel.Sporadic.SuzK.Keys
public import Certificates.Kernel.Sporadic.SuzK.RelK
public import CFSG.Sporadic.SuzOddCore.RelabelCheckInputs
import Certificates.Kernel.Sporadic.SuzK.Conj
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzK.relAll CertificateChecks.KernelSpor.SuzK.relSl 10

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.Row CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Th.Native CertificateChecks.KernelSpor.OddCore

theorem rel_lt {i : Nat} (hi : i < 22880) : r15 SuzRelT.F 0 i < 22880 := by
  have h := relabel_perm
  unfold rpermK at h
  have h' := Raw.Orb.allN_iff.1 h i hi
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h'
  exact h'.1

theorem rel_pt {i : Nat} (hi : i < 22880) :
    r15 SuzRelT.F 0 (r32 AL i) = r15 SuzCertT.F 0 (r15 SuzRelT.F 0 i) ∧
      r15 SuzRelT.F 0 (r32 BE i) = r15 SuzCertT.F 715 (r15 SuzRelT.F 0 i) := by
  have hs : i / 2288 < 10 := by omega
  have h := relAll (i / 2288) hs
  unfold relSl at h
  rw [Raw.Orb.strictB_eq] at h
  have h' := Raw.Orb.allN_iff.1 h (i % 2288) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 2288) 2288) (i % 2288) = i := by
    change i / 2288 * 2288 + i % 2288 = i
    omega
  rw [Raw.Orb.strictB_eq, e, Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hi)] at h'
  unfold relAt at h'
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩

theorem relabel_ok : relabelOK (CFSG.Sporadic.Suz.Native.orbitData ()).alpha
    (CFSG.Sporadic.Suz.Native.orbitData ()).beta = true := by
  rw [orbitData_eq]
  unfold relabelOK
  dsimp only
  rw [relabelArr_eq, certArr_eq (k := 0) (by norm_num), certArr_eq (k := 1) (by norm_num)]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨(tabOf_size AL : (tabOf AL).size = 22880), (tabOf_size BE : (tabOf BE).size = 22880)⟩, ?_⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  have hr : rg 15 (mask 15) SuzRelT.F 0 i < 22880 := rel_lt hi
  rw [alpha_ap hi, beta_ap hi, rowArr_get (al_lt hi), rowArr_get (be_lt hi), rowArr_get hi,
    rowArr_get hr, rowArr_get hr]
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.mul_zero, Nat.mul_one]
  exact rel_pt hi

end CertificateChecks.KernelSpor.SuzK

end
