module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.J3K.Data
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.J3.Group
public import Certificates.Data.CFSGNative.J3.Data
public import CFSG.Certificates.Kernel.Bounds.J3Alt.RelsTC
public import CFSG.Certificates.Kernel.Orders.J3.RelsBind
public import CFSG.Certificates.Kernel.Orders.J3.Checks.R
public import CFSG.Certificates.Kernel.Orders.J3.Checks.H
public import CFSG.Certificates.Kernel.Orders.J3.Checks.D
public import CFSG.Certificates.Kernel.Orders.J3.Checks.K
public import CFSG.Certificates.Kernel.Orders.J3.Data.Pay
public import CFSG.Certificates.Kernel.Orders.J3.Data.Sel
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.J3 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

local notation "Dt" => CFSG.Sporadic.J3.Native.j3Data

local notation "Mt" =>
  Matrix (Fin 80) (Fin 80) (ZMod 2)

local notation "GLt" =>
  GL (Fin 80) (ZMod 2)

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK J3SeedA.chars CFSG.KD.OrdJ3.P1 256 6501 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK J3SeedB.chars CFSG.KD.OrdJ3.P2 256 6501 = true := by
  quickRfl

noncomputable abbrev X (g : Nat) : Mt := ordMat 2 80 8 640 (CFSG.KD.OrdJ3.RH g)

noncomputable abbrev Y (M : Nat) : Mt := ordMat 2 80 8 640 M

noncomputable abbrev mat (g : J Dt) : Mt := (((g : GLt) : Mt))

theorem mat_def (g : J Dt) : mat g = ((g : GLt) : Mt) := rfl

theorem mat_mul (g h : J Dt) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J Dt) = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ e => Subtype.ext (Units.ext e)

theorem hAB' : CFSG.KD.OrdJ3.RH 1 = CFSG.KD.OrdJ3.RW 1 ∧
    CFSG.KD.OrdJ3.RH 2 = CFSG.KD.OrdJ3.RW 2 := by
  have h := (andB_iff _ _).1 CFSG.KD.OrdJ3.hAB
  have h2 := (andB_iff _ _).1 h.2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem mA_eq : mA Dt = X 1 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdJ3.consts seed1_bytes (by decide)
    (decRun_join CFSG.KD.OrdJ3.d1_0 CFSG.KD.OrdJ3.d1_16) CFSG.KD.OrdJ3.d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 80 1 CFSG.Sporadic.J3.Native.seedA = _
  rw [J3SeedA.eq, h, ← hAB'.1]

theorem mB_eq : mB Dt = X 2 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdJ3.consts seed2_bytes (by decide)
    (decRun_join CFSG.KD.OrdJ3.d2_0 CFSG.KD.OrdJ3.d2_16) CFSG.KD.OrdJ3.d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 80 1 CFSG.Sporadic.J3.Native.seedB = _
  rw [J3SeedB.eq, h, ← hAB'.2]

theorem hom : (∀ g < 2, X (g + 1) * X (2 + 1 + g) = 1) ∧
    ∀ v ∈ CFSG.KD.OrdJ3.rels, (v.map fun x => Y (letM CFSG.KD.OrdJ3.RH 2 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdJ3.consts CFSG.KD.OrdJ3.hroots CFSG.KD.OrdJ3.hinv
    CFSG.KD.OrdJ3.relB fun r hr => ?_
  have hn : lenRels CFSG.KD.OrdJ3.rels = 8 := Nat.eq_of_beq_eq_true CFSG.KD.OrdJ3.relN
  rw [hn] at hr
  exact Or.inl (CFSG.KD.OrdJ3.R.all r hr)

theorem det_mA : (mA Dt).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hom.1 0 (by norm_num))
  rw [Matrix.det_mul, Matrix.det_one, ← mA_eq, h0, zero_mul] at h
  exact zero_ne_one h

theorem det_mB : (mB Dt).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hom.1 1 (by norm_num))
  rw [Matrix.det_mul, Matrix.det_one, ← mB_eq, h0, zero_mul] at h
  exact zero_ne_one h

theorem mat_a' : mat (a Dt) = X 1 := by
  have h1 : ((a Dt : GLt)) = gA Dt := by
    unfold a
    exact Subtype.coe_mk _ _
  have h2 : ((gA Dt : GLt) : Mt) = mA Dt := by
    rw [gA]
    exact coe_dite_mk _ det_mA
  rw [mat_def, h1, h2, mA_eq]

theorem mat_b' : mat (b Dt) = X 2 := by
  have h1 : ((b Dt : GLt)) = gB Dt := by
    unfold b
    exact Subtype.coe_mk _ _
  have h2 : ((gB Dt : GLt) : Mt) = mB Dt := by
    rw [gB]
    exact coe_dite_mk _ det_mB
  rw [mat_def, h1, h2, mB_eq]

theorem matInv_a : mat (a Dt)⁻¹ = X 3 := by
  have h1 : X 1 * X 3 = 1 := hom.1 0 (by norm_num)
  have h2 : mat (a Dt)⁻¹ * mat (a Dt) = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_a'] at h2
  calc mat (a Dt)⁻¹ = mat (a Dt)⁻¹ * (X 1 * X 3) := by rw [h1, Matrix.mul_one]
    _ = X 3 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem matInv_b : mat (b Dt)⁻¹ = X 4 := by
  have h1 : X 2 * X 4 = 1 := hom.1 1 (by norm_num)
  have h2 : mat (b Dt)⁻¹ * mat (b Dt) = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_b'] at h2
  calc mat (b Dt)⁻¹ = mat (b Dt)⁻¹ * (X 2 * X 4) := by rw [h1, Matrix.mul_one]
    _ = X 4 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mat_letter (x : Nat × Bool) (hx : x.1 < 2) :
    mat (if x.2 then img2 (a Dt) (b Dt) x.1 else (img2 (a Dt) (b Dt) x.1)⁻¹) =
      Y (letM CFSG.KD.OrdJ3.RH 2 x) := by
  obtain ⟨g, s⟩ := x
  simp only at hx
  interval_cases g <;> cases s <;> simp [img2, letM, matInv_a, matInv_b, mat_a', mat_b']

theorem relators : ∀ v ∈ TauCeti.Sporadic.j3Presentation.relatorLetters,
    wordProd (img2 (a Dt) (b Dt)) v = 1 := by
  rw [CFSG.KC.J3A.rels_eq, ← CFSG.KD.OrdJ3.rels_eq]
  intro v hv
  apply mat_injective
  rw [mat_one]
  have hb := relsBounded_spec CFSG.KD.OrdJ3.relB v hv
  have hm : ∀ l : List (J Dt), mat l.prod = (l.map mat).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]
  rw [wordProd, hm, List.map_map, ← hom.2 v hv]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact mat_letter x (hb x hx)

end CertificateChecks.KernelSpor.J3Rels

end
