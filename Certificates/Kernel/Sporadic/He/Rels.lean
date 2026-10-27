module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Certificates.Kernel.Orders.He.RelsBind
public import CFSG.Certificates.Kernel.Orders.He.Checks.R
public import CFSG.Certificates.Kernel.Orders.He.Checks.H
public import CFSG.Certificates.Kernel.Orders.He.Checks.D
public import CFSG.Certificates.Kernel.Orders.He.Checks.K
public import CFSG.Certificates.Kernel.Orders.He.Data.Pay
public import CFSG.Certificates.Kernel.Orders.He.Data.Sel
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed1

#ks_chars CertificateChecks.KernelSpor.HeSeed2 CFSG.Blueprint.NativeSporadic.HeSeed2

namespace CertificateChecks.KernelSpor.HeRels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.He CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK HeSeed1.chars CFSG.KD.OrdHe.P1 256 2571 =
    true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK HeSeed2.chars CFSG.KD.OrdHe.P2 256 2571 =
    true := by quickRfl

noncomputable abbrev X (g : Nat) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  ordMat 7 50 12 600 (CFSG.KD.OrdHe.RH g)

noncomputable abbrev Y (M : Nat) : Matrix (Fin 50) (Fin 50) (ZMod 7) := ordMat 7 50 12 600 M

theorem hAB' : CFSG.KD.OrdHe.RH 1 = CFSG.KD.OrdHe.RW 1 ∧
    CFSG.KD.OrdHe.RH 2 = CFSG.KD.OrdHe.RW 2 := by
  have h := (andB_iff _ _).1 CFSG.KD.OrdHe.hAB
  have h2 := (andB_iff _ _).1 h.2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem mA_eq : mA = X 1 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdHe.consts seed1_bytes (by decide)
    CFSG.KD.OrdHe.d1_0 CFSG.KD.OrdHe.d1_end
  change CFSG.Blueprint.NativeSporadic.decode 7 50 1 CFSG.Blueprint.NativeSporadic.HeSeed1 = _
  rw [HeSeed1.eq, h, ← hAB'.1]

theorem mB_eq : mB = X 2 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdHe.consts seed2_bytes (by decide)
    CFSG.KD.OrdHe.d2_0 CFSG.KD.OrdHe.d2_end
  change CFSG.Blueprint.NativeSporadic.decode 7 50 1 CFSG.Blueprint.NativeSporadic.HeSeed2 = _
  rw [HeSeed2.eq, h, ← hAB'.2]

theorem hom : (∀ g < 2, X (g + 1) * X (2 + 1 + g) = 1) ∧
    ∀ v ∈ CFSG.KD.OrdHe.rels, (v.map fun x => Y (letM CFSG.KD.OrdHe.RH 2 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdHe.consts CFSG.KD.OrdHe.hroots CFSG.KD.OrdHe.hinv
    CFSG.KD.OrdHe.relB fun r hr => ?_
  have hn : lenRels CFSG.KD.OrdHe.rels = 7 := Nat.eq_of_beq_eq_true CFSG.KD.OrdHe.relN
  rw [hn] at hr
  exact Or.inl (CFSG.KD.OrdHe.R.all r hr)

theorem mat_a' : mat a = X 1 := by
  rw [← mA_eq]
  rfl

theorem mat_b' : mat b = X 2 := by
  rw [← mB_eq]
  rfl

theorem matInv_a : mat a⁻¹ = X 3 := by
  have h1 : X 1 * X 3 = 1 := hom.1 0 (by norm_num)
  have h2 : mat a⁻¹ * mat a = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_a'] at h2
  calc mat a⁻¹ = mat a⁻¹ * (X 1 * X 3) := by rw [h1, Matrix.mul_one]
    _ = X 3 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem matInv_b : mat b⁻¹ = X 4 := by
  have h1 : X 2 * X 4 = 1 := hom.1 1 (by norm_num)
  have h2 : mat b⁻¹ * mat b = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_b'] at h2
  calc mat b⁻¹ = mat b⁻¹ * (X 2 * X 4) := by rw [h1, Matrix.mul_one]
    _ = X 4 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mat_letter (x : Nat × Bool) (hx : x.1 < 2) :
    mat (if x.2 then img2 a b x.1 else (img2 a b x.1)⁻¹) = Y (letM CFSG.KD.OrdHe.RH 2 x) := by
  obtain ⟨g, s⟩ := x
  simp only at hx
  interval_cases g <;> cases s <;> simp [img2, letM, matInv_a, matInv_b, mat_a', mat_b']

theorem relators :
    ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters, wordProd (img2 a b) v = 1 := by
  rw [CFSG.KD.OrdHe.rels_eq]
  intro v hv
  apply mat_injective
  rw [mat_one]
  have hb := relsBounded_spec CFSG.KD.OrdHe.relB v hv
  have hm : ∀ l : List J, mat l.prod = (l.map mat).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]
  rw [wordProd, hm, List.map_map, ← hom.2 v hv]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact mat_letter x (hb x hx)

end CertificateChecks.KernelSpor.HeRels

end
