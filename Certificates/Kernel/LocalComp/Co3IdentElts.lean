
module

public import Certificates.Kernel.LocalComp.Co3IdentHR
public import Certificates.Kernel.LocalComp.Co3IdentCR
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCubeInputs
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCubeInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelLC.Co3Id.YP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.yArr
#ks_perm CertificateChecks.KernelLC.Co3Id.EAP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.eaArr
#ks_perm CertificateChecks.KernelLC.Co3Id.BCBP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.bcbArr
#ks_perm CertificateChecks.KernelLC.Co3Id.KPP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.kpArr
#ks_perm CertificateChecks.KernelLC.Co3Id.UP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.uArr
#ks_perm CertificateChecks.KernelLC.Co3Id.KPCP 9 CFSG.EvenSmallLie.SympSix.Co3Ident.kpcArr

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelLC CertificateChecks.KernelSpor

abbrev Cn (X : Nat) : Prop := canonK 276 9 (mask 9) (276 * 9) X = true

theorem compA_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 276 (unpack 276 9 p) (unpack 276 9 q) = unpack 276 9 (pc p q) := by
  apply compEqK_sound
  unfold compEqK
  rw [hp, hq]
  exact Nat.beq_refl _

theorem comm_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    commutesA 276 (unpack 276 9 p) (unpack 276 9 q) = Nat.beq (pc p q) (pc q p) := by
  unfold commutesA
  rw [compA_unpack hp hq, compA_unpack hq hp, eqA_unpack (canon_pc hp hq) (canon_pc hq hp)]

theorem kCid : Cn (pidn 276 9) := by quickRfl

theorem eqA_idA {p : Nat} (hp : Cn p) :
    eqA 276 (unpack 276 9 p) (idA 276) = Nat.beq p (pidn 276 9) := by
  rw [← idK_sound kId, eqA_unpack hp kCid]

theorem wordP_canon : ∀ (w : List (Fin 7 × Bool)), wordOK w = true → Cn (wordP w)
  | [], _ => kCid
  | l :: w, h => by
    obtain ⟨h1, _⟩ := (bAnd_iff _ _).1 h
    unfold prodOK compEqK at h1
    obtain ⟨c1, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨c2, _⟩ := (bAnd_iff _ _).1 h1
    exact canon_pc c1 c2

theorem kCP : allN 7 (fun i => canonK 276 9 (mask 9) (276 * 9) (P i)) = true := by quickRfl

theorem cP (i : Nat) (hi : i < 7) : Cn (P i) := allN_spec kCP i hi

theorem cHR (j : Nat) (hj : j < 4608) : Cn (HR.E j) := (hAll_spec j (by rw [hc]; exact hj)).1

theorem cCR (j : Nat) (hj : j < 630) : Cn (CR.E j) := (cAll_spec j (by rw [cc]; exact hj)).1

theorem cG (i : Nat) (hi : i < 3) : Cn (HR.G i) := allN_spec kGc i hi

theorem kYb : Nat.beq (pc (pc P0 P2) P4) YP = true := by quickRfl
theorem kEAb : Nat.beq (pc P4 P0) EAP = true := by quickRfl
theorem kBCBw : wordOK (pos [1, 2, 1]) = true := by quickRfl
theorem kBCBb : Nat.beq (wordP (pos [1, 2, 1])) BCBP = true := by quickRfl
theorem kKPw : wordOK (pos kpWord) = true := by quickRfl
theorem kKPb : Nat.beq (wordP (pos kpWord)) KPP = true := by quickRfl
theorem kUb : Nat.beq (pc BCBP P3) UP = true := by quickRfl
theorem kKPCb : Nat.beq (pc KPP P2) KPCP = true := by quickRfl

theorem c0 : Cn P0 := cP 0 (by omega)
theorem c2 : Cn P2 := cP 2 (by omega)
theorem c3 : Cn P3 := cP 3 (by omega)
theorem c4 : Cn P4 := cP 4 (by omega)
theorem c5 : Cn P5 := cP 5 (by omega)

theorem cY : Cn YP := by
  rw [← Nat.eq_of_beq_eq_true kYb]
  exact canon_pc (canon_pc c0 c2) c4

theorem cEA : Cn EAP := by
  rw [← Nat.eq_of_beq_eq_true kEAb]
  exact canon_pc c4 c0

theorem cBCB : Cn BCBP := by
  rw [← Nat.eq_of_beq_eq_true kBCBb]
  exact wordP_canon _ kBCBw

theorem cKP : Cn KPP := by
  rw [← Nat.eq_of_beq_eq_true kKPb]
  exact wordP_canon _ kKPw

theorem cU : Cn UP := by
  rw [← Nat.eq_of_beq_eq_true kUb]
  exact canon_pc cBCB c3

theorem cKPC : Cn KPCP := by
  rw [← Nat.eq_of_beq_eq_true kKPCb]
  exact canon_pc cKP c2

theorem y_eq : yArr = unpack 276 9 YP := by
  unfold yArr
  rw [bind0, bind2, bind4, compA_unpack c0 c2, compA_unpack (canon_pc c0 c2) c4,
    Nat.eq_of_beq_eq_true kYb]

theorem ea_eq : eaArr = unpack 276 9 EAP := by
  unfold eaArr
  rw [bind4, bind0, compA_unpack c4 c0, Nat.eq_of_beq_eq_true kEAb]

theorem bcb_eq : bcbArr = unpack 276 9 BCBP := by
  unfold bcbArr posArr
  rw [wordArr_eq _ kBCBw, Nat.eq_of_beq_eq_true kBCBb]

theorem kp_eq : kpArr = unpack 276 9 KPP := by
  unfold kpArr posArr
  rw [wordArr_eq _ kKPw, Nat.eq_of_beq_eq_true kKPb]

theorem u_eq : uArr = unpack 276 9 UP := by
  unfold uArr
  rw [bcb_eq, bind3, compA_unpack cBCB c3, Nat.eq_of_beq_eq_true kUb]

theorem kpc_eq : kpcArr = unpack 276 9 KPCP := by
  unfold kpcArr
  rw [kp_eq, bind2, compA_unpack cKP c2, Nat.eq_of_beq_eq_true kKPCb]

end CertificateChecks.KernelLC.Co3Id

end
