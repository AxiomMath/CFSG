module

public import CFSG.Sporadic.HS.Group
public import CFSG.Sporadic.Bridge.TwoGen

public section

namespace CertificateChecks.KernelSpor.SmallF2Rels

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

variable (D : CFSG.Sporadic.SmallF2.Native.VecData)

@[expose] noncomputable def mat (g : J D) : Matrix (Fin D.d) (Fin D.d) (ZMod 2) :=
  ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2))

theorem mat_mul (g h : J D) : mat D (g * h) = mat D g * mat D h := rfl

theorem mat_one : mat D 1 = 1 := rfl

theorem mat_injective : Function.Injective (mat D) := fun _ _ e => Subtype.ext (Units.ext e)

theorem mat_prod (l : List (J D)) : mat D l.prod = (l.map (mat D)).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]

theorem mat_inv {g : J D} {M N : Matrix (Fin D.d) (Fin D.d) (ZMod 2)} (hg : mat D g = M)
    (h : M * N = 1) : mat D g⁻¹ = N := by
  have h2 : mat D g⁻¹ * M = 1 := by rw [← hg, ← mat_mul, inv_mul_cancel, mat_one]
  calc mat D g⁻¹ = mat D g⁻¹ * (M * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem det_ne_zero {M N : Matrix (Fin D.d) (Fin D.d) (ZMod 2)} (h : M * N = 1) : M.det ≠ 0 := by
  intro h0
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h'
  exact zero_ne_one h'

theorem mat_a {N : Matrix (Fin D.d) (Fin D.d) (ZMod 2)} (h : mA D * N = 1) :
    mat D (a D) = mA D := by
  have h1 : ((a D : J D) : GL (Fin D.d) (ZMod 2)) = gA D := rfl
  rw [mat, h1, gA, dite_eq_left (det_ne_zero D h)]
  rfl

theorem mat_b {N : Matrix (Fin D.d) (Fin D.d) (ZMod 2)} (h : mB D * N = 1) :
    mat D (b D) = mB D := by
  have h1 : ((b D : J D) : GL (Fin D.d) (ZMod 2)) = gB D := rfl
  rw [mat, h1, gB, dite_eq_left (det_ne_zero D h)]
  rfl

theorem relators_of (rels : List (List (Nat × Bool)))
    (X Y : Nat → Matrix (Fin D.d) (Fin D.d) (ZMod 2)) (L : Nat × Bool → Nat)
    (hA : mA D = X 1) (hB : mB D = X 2) (h13 : X 1 * X 3 = 1) (h24 : X 2 * X 4 = 1)
    (hL : ∀ g s, g < 2 → Y (L (g, s)) = Bool.rec (X (2 + 1 + g)) (X (g + 1)) s)
    (hb : ∀ v ∈ rels, ∀ x ∈ v, x.1 < 2)
    (hrel : ∀ v ∈ rels, (v.map fun x => Y (L x)).prod = 1) :
    ∀ v ∈ rels, wordProd (img2 (a D) (b D)) v = 1 := by
  have ha : mat D (a D) = X 1 := by rw [mat_a D (N := X 3) (by rw [hA]; exact h13), hA]
  have hb' : mat D (b D) = X 2 := by rw [mat_b D (N := X 4) (by rw [hB]; exact h24), hB]
  have hai := mat_inv D ha h13
  have hbi := mat_inv D hb' h24
  intro v hv
  apply mat_injective D
  rw [mat_one, wordProd, mat_prod, List.map_map, ← hrel v hv]
  congr 1
  apply List.map_congr_left
  intro x hx
  obtain ⟨g, s⟩ := x
  have hg : g < 2 := hb v hv _ hx
  rw [Function.comp_apply, hL g s hg]
  interval_cases g <;> cases s <;> simp [img2, ha, hb', hai, hbi]

end CertificateChecks.KernelSpor.SmallF2Rels

end
