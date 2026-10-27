
module

public import Certificates.Kernel.Sporadic.Fi22.F3151R
public import Certificates.Kernel.Sporadic.Fi22.C2068Base
public import Certificates.Kernel.Sporadic.Fi22.C3150
public import CFSG.Certificates.Kernel.Spor.Coords3Sound
public import CFSG.Monster.B.Fischer.Fi22CoverBase
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSiftK

@[expose] public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.Fi22F2.treeAll CertificateChecks.KernelSpor.Fi22F2.treeSl 7

#kon_join CertificateChecks.KernelSpor.Fi22F2.rootAll CertificateChecks.KernelSpor.Fi22F2.rootSl 9

#kon_join CertificateChecks.KernelSpor.Fi22F2.hAll CertificateChecks.KernelSpor.Fi22F2.hSl 9

namespace CertificateChecks.KernelSpor.Fi22C3151

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22F2
open CertificateChecks.KernelSpor.Fi22LabA (unpack_get' strictB_eq' tr3_eq tlev offs_parts)

theorem div_eq' (a b : Nat) : Nat.div a b = a / b := rfl

theorem mod_eq' (a b : Nat) : Nat.mod a b = a % b := rfl

@[expose] def xN (I : Nat) : Nat × Nat × Nat := (I / 128, I / 4 % 32, I % 4)

@[expose] def xF (I : Nat) : Fin 1024 × Fin 32 × Fin 4 :=
  (⟨I / 128 % 1024, Nat.mod_lt _ (by norm_num)⟩, ⟨I / 4 % 32, Nat.mod_lt _ (by norm_num)⟩,
    ⟨I % 4, Nat.mod_lt _ (by norm_num)⟩)

@[expose] def iX (x : Fin 1024 × Fin 32 × Fin 4) : Nat := (x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val

theorem iX_lt (x : Fin 1024 × Fin 32 × Fin 4) : iX x < 131072 := by
  have := x.1.2
  have := x.2.1.2
  have := x.2.2.2
  unfold iX
  omega

theorem xF_iX (x : Fin 1024 × Fin 32 × Fin 4) : xF (iX x) = x := by
  have := x.1.2
  have := x.2.1.2
  have := x.2.2.2
  obtain ⟨a, b, c⟩ := x
  unfold xF iX
  simp only [Prod.mk.injEq, Fin.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp only at * <;> omega

theorem iX_xF {I : Nat} (h : I < 131072) : iX (xF I) = I := by
  unfold xF iX
  simp only
  omega

theorem xF_val {I : Nat} (h : I < 131072) :
    ((xF I).1.val, (xF I).2.1.val, (xF I).2.2.val) = xN I := by
  simp only [xF, xN, Prod.mk.injEq]
  exact ⟨Nat.mod_eq_of_lt (by omega : I / 128 < 1024), trivial⟩

theorem bT_lt {t : Nat} (ht : t < 6) : bT t < 3510 := by
  interval_cases t <;> decide

theorem g3_eq {a b c p : Nat} (ha : a < 1024) (hb : b < 32) (hc : c < 4) (hp : p < 3510) :
    g3 a b c p = tr3 fi22TLevels a b c p := (tr3_eq ha hb hc hp).symm

theorem blt_t {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.blt_eq ▸ h

theorem t_blt {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.blt_eq ▸ h

@[expose] def ScanOK : Prop := ∀ I < 131072, scanRow I = true

theorem bIf_true {c : Bool} {t e : Bool} (h : bIf(c, t, e) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem bIf_false {c : Bool} {t e : Bool} (h : bIf(c, t, e) = true) (hc : c = false) : e = true := by
  subst hc
  exact h

theorem scan_parts {I : Nat} (h : scanRow I = true) :
    (invB (I / 128) (I / 4 % 32) (I % 4) = true → PPf I < 3263 ∧ SV (PPf I) = I) ∧
      (invB (I / 128) (I / 4 % 32) (I % 4) = false → PPf I = 3263) ∧
      (I ≠ 0 → movB (I / 128) (I / 4 % 32) (I % 4) = true) := by
  unfold scanRow at h
  rw [strictB_eq', strictB_eq', strictB_eq'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq'] at h1
  refine ⟨fun hi => ?_, fun hi => Nat.eq_of_beq_eq_true (bIf_false h1 hi), fun hI => ?_⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (bIf_true h1 hi)
    exact ⟨blt_t a, Nat.eq_of_beq_eq_true b⟩
  · have : Nat.beq I 0 = false := by
      cases e : Nat.beq I 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hI
    exact bIf_false h2 this

theorem sv_parts {k : Nat} (hk : k < 3263) : SV k < 131072 ∧ PPf (SV k) = k := by
  have h := allN_spec (treeAll (k / 512) (by change k / 512 < 7; omega)) (k % 512) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq'] at h
  have e : Nat.add (Nat.mul (k / 512) 512) (k % 512) = k := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  have hb : Nat.blt k 3263 = true := t_blt hk
  obtain ⟨hs, -⟩ := (bAnd_iff _ _).1 (bIf_true h hb)
  unfold svRow at hs
  rw [strictB_eq'] at hs
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 hs
  exact ⟨blt_t a, Nat.eq_of_beq_eq_true b⟩

theorem tree_parts {k : Nat} (hk : k < 3263) : treeRow k = true := by
  have h := allN_spec (treeAll (k / 512) (by change k / 512 < 7; omega)) (k % 512) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq'] at h
  have e : Nat.add (Nat.mul (k / 512) 512) (k % 512) = k := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  have hb : Nat.blt k 3263 = true := t_blt hk
  exact ((bAnd_iff _ _).1 (bIf_true h hb)).2

end CertificateChecks.KernelSpor.Fi22C3151

end
