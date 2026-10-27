module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Fi22.Setup
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Certificates.Kernel.Orders.Fi22.RelsBind
public import CFSG.Certificates.Kernel.Orders.Fi22.Checks.R
public import CFSG.Certificates.Kernel.Orders.Fi22.Checks.H
public import CFSG.Certificates.Kernel.Orders.Fi22.Checks.D
public import CFSG.Certificates.Kernel.Orders.Fi22.Checks.K
public import CFSG.Certificates.Kernel.Orders.Fi22.Data.Pay
public import CFSG.Certificates.Kernel.Orders.Fi22.Data.Sel
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22Seed1 CFSG.Blueprint.NativeSporadic.Fi22Seed1

#ks_chars CertificateChecks.KernelSpor.Fi22Seed2 CFSG.Blueprint.NativeSporadic.Fi22Seed2

namespace CertificateChecks.KernelSpor.Fi22Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.Fi22 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK Fi22Seed1.chars CFSG.KD.OrdFi22.P1 256 6027 =
    true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK Fi22Seed2.chars CFSG.KD.OrdFi22.P2 256 6027 =
    true := by quickRfl

noncomputable abbrev X (g : Nat) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  ordMat 3 77 10 770 (CFSG.KD.OrdFi22.RH g)

noncomputable abbrev Y (M : Nat) : Matrix (Fin 77) (Fin 77) (ZMod 3) := ordMat 3 77 10 770 M

theorem hAB' : CFSG.KD.OrdFi22.RH 1 = CFSG.KD.OrdFi22.RW 1 ∧
    CFSG.KD.OrdFi22.RH 2 = CFSG.KD.OrdFi22.RW 2 := by
  have h := (andB_iff _ _).1 CFSG.KD.OrdFi22.hAB
  have h2 := (andB_iff _ _).1 h.2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem mA_eq : mA = X 1 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdFi22.consts seed1_bytes (by decide)
    (decRun_join CFSG.KD.OrdFi22.d1_0 CFSG.KD.OrdFi22.d1_16) CFSG.KD.OrdFi22.d1_end
  change CFSG.Blueprint.NativeSporadic.decode 3 77 1 CFSG.Blueprint.NativeSporadic.Fi22Seed1 = _
  rw [Fi22Seed1.eq, h, ← hAB'.1]

theorem mB_eq : mB = X 2 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdFi22.consts seed2_bytes (by decide)
    (decRun_join CFSG.KD.OrdFi22.d2_0 CFSG.KD.OrdFi22.d2_16) CFSG.KD.OrdFi22.d2_end
  change CFSG.Blueprint.NativeSporadic.decode 3 77 1 CFSG.Blueprint.NativeSporadic.Fi22Seed2 = _
  rw [Fi22Seed2.eq, h, ← hAB'.2]

theorem hom : (∀ g < 2, X (g + 1) * X (2 + 1 + g) = 1) ∧
    ∀ v ∈ CFSG.KD.OrdFi22.rels, (v.map fun x => Y (letM CFSG.KD.OrdFi22.RH 2 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdFi22.consts CFSG.KD.OrdFi22.hroots
    CFSG.KD.OrdFi22.hinv CFSG.KD.OrdFi22.relB fun r hr => ?_
  have hn : lenRels CFSG.KD.OrdFi22.rels = 13 := Nat.eq_of_beq_eq_true CFSG.KD.OrdFi22.relN
  rw [hn] at hr
  exact Or.inl (CFSG.KD.OrdFi22.R.all r hr)

noncomputable abbrev mat (g : J) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  ((g : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_injective : Function.Injective mat :=
  fun _ _ e => Subtype.ext (Units.ext e)

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
    mat (if x.2 then img2 a b x.1 else (img2 a b x.1)⁻¹) = Y (letM CFSG.KD.OrdFi22.RH 2 x) := by
  obtain ⟨g, s⟩ := x
  simp only at hx
  interval_cases g <;> cases s <;> simp [img2, letM, matInv_a, matInv_b, mat_a', mat_b']

theorem relators :
    ∀ v ∈ TauCeti.Sporadic.fi22Presentation.relatorLetters, wordProd (img2 a b) v = 1 := by
  rw [CFSG.KD.OrdFi22.rels_eq]
  intro v hv
  apply mat_injective
  rw [mat_one]
  have hb := relsBounded_spec CFSG.KD.OrdFi22.relB v hv
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

theorem neg_rel : notB (relOK CFSG.KD.OrdFi22.RH
    (mulR 3 10 770 77 7 CFSG.KD.OrdFi22.L CFSG.KD.OrdFi22.H CFSG.KD.OrdFi22.CM CFSG.KD.OrdFi22.RM)
    [[(0, true)]] 2 CFSG.KD.OrdFi22.ONE 0) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22Rels

end
