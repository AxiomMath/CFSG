
module

public import Certificates.Kernel.Sporadic.Fi24Br.Img
public import Certificates.Kernel.Sporadic.Fi24Fix.Data
public import CFSG.Certificates.Kernel.Spor.Fi24FixCoset
public import CFSG.Certificates.Kernel.Spor.Fi24FixInit
import Certificates.Kernel.Sporadic.Fi24Fix.Chain
import Certificates.Kernel.Sporadic.Fi24Fix.Stab
import Certificates.Kernel.Sporadic.Fi24Fix.Init
import Certificates.Kernel.Sporadic.Fi24Fix.MA

public section

namespace CertificateChecks.KernelFi24Fix

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24 CFSG.KS.Mat3 CertificateChecks.KernelHomG
  CertificateChecks.KernelWP CertificateChecks.KernelWPX CertificateChecks.KernelSpor.Fi24Rels
  CFSG.KC.Fi24FixC CFSG.KD.Fi24Fix

noncomputable abbrev V0 : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  LinearMap.range (mat3 781 609961 CFSG.KD.Fi24Fix.Q).mulVecLin

@[expose] def pv : List (ℕ × Bool) :=
  [(8, false), (5, true), (4, false), (3, true), (2, false), (1, true), (0, false), (9, false),
    (10, true), (6, false), (7, true), (2, false), (6, true), (3, false), (2, true), (1, false),
    (0, true), (9, true), (2, false), (6, true), (3, false), (4, true), (2, false), (3, true),
    (1, false), (2, true), (6, false), (1, true), (0, false)]

@[expose] def regIdx (l : ℕ × Bool) : ℕ :=
  Prod.rec (motive := fun _ => ℕ) (fun g s => Bool.rec (motive := fun _ => ℕ) (Nat.add (Nat.succ 11) g)
    (Nat.succ g) s) l

theorem regIdx_eq (l : ℕ × Bool) : RB (regIdx l) = letM RB 11 l := rfl

theorem pv_regs : pv.map regIdx = CFSG.KD.Fi24Fix.W := by decide

theorem pv_lt : ∀ l ∈ pv, l.1 < 11 := by decide

theorem canon_letM {l : ℕ × Bool} (hl : l.1 < 11) : Canon3 609961 (letM RB 11 l) :=
  letM_q hs hroot hinv hl

theorem canon_of_vld {X : ℕ} (h : VLD X = true) : Canon3 609961 X := hs.vld_q X h

theorem wordMul_mat {Y : ℕ} (hY : Canon3 609961 Y) : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 11) →
    Canon3 609961 (wordMul MUL RB (w.map regIdx) Y) ∧
      mat3 781 609961 (wordMul MUL RB (w.map regIdx) Y) =
        (w.map fun l => mat3 781 609961 (letM RB 11 l)).prod * mat3 781 609961 Y
  | [], _ => ⟨hY, by simp [wordMul]⟩
  | l :: w, hw => by
    obtain ⟨h1, h2⟩ := wordMul_mat hY w (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := canon_letM (hw l List.mem_cons_self)
    have e : wordMul MUL RB ((l :: w).map regIdx) Y =
        MUL (letM RB 11 l) (wordMul MUL RB (w.map regIdx) Y) := rfl
    obtain ⟨h3, h4⟩ := hs.mul_sound _ _ hl h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.map_cons, List.prod_cons, Matrix.mul_assoc]

theorem range_mul (A B : Matrix (Fin 781) (Fin 781) (ZMod 3)) :
    LinearMap.range (A * B).mulVecLin = (LinearMap.range B.mulVecLin).map A.mulVecLin := by
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]

theorem range_le_of_mul_eq {A B : Matrix (Fin 781) (Fin 781) (ZMod 3)} (h : A * B = B) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [← h, range_mul]
  exact LinearMap.map_le_range

theorem keeps_stab {u : GL (Fin 781) (ZMod 3)} {X : ℕ} (hX : Canon3 609961 X)
    (hu : u.val = mat3 781 609961 X) (h : keepsOK MUL Q X = true) : u ∈ stab V0 := by
  have hQ : Canon3 609961 Q := canon_of_vld (andB_true3 (andB_true3 (andB_true3 valid).2).2).1
  obtain ⟨hXQ, eXQ⟩ := hs.mul_sound _ _ hX hQ
  have h' : MUL Q (MUL X Q) = MUL X Q := by
    unfold keepsOK at h
    rw [strictN_eq3, Nat.beq_eq] at h
    cases hb : Nat.beq (MUL Q (MUL X Q)) (MUL X Q)
    · rw [hb] at h
      exact absurd h (by decide)
    · exact Nat.eq_of_beq_eq_true hb
  obtain ⟨-, e2⟩ := hs.mul_sound _ _ hQ hXQ
  rw [h'] at e2
  have hle : act u V0 ≤ V0 := by
    unfold act
    rw [hu, ← range_mul, ← eXQ]
    exact range_le_of_mul_eq e2.symm
  rw [mem_stab]
  have hinj : Function.Injective (Matrix.mulVecLin (u : Matrix (Fin 781) (Fin 781) (ZMod 3))) := by
    intro v w hvw
    have := congrArg (Matrix.mulVecLin ((u⁻¹ : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))) hvw
    simpa [Matrix.mulVec_mulVec] using this
  have hcoe : ((act u V0 : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : Set (Fin 781 → ZMod 3)) =
      (Matrix.mulVecLin (u : Matrix (Fin 781) (Fin 781) (ZMod 3))) '' V0 := Submodule.map_coe _ _
  have hsub : ((act u V0 : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : Set (Fin 781 → ZMod 3)) ⊆ V0 := hle
  have e := Set.eq_of_subset_of_ncard_le hsub (by rw [hcoe, Set.ncard_image_of_injective _ hinj])
    (Set.toFinite _)
  exact SetLike.coe_injective e

theorem root_eq : LinearMap.range (mat3 781 609961 R).mulVecLin = (CFSG.Sporadic.Fi24.pt 0).sp :=
  CFSG.KC.Fi24FixS.span_eq_pt_zero (pow_sub_one_eq 609961) IA.eq init_digits init_cols init_rows

theorem matFacts : ∃ x : ℕ → GL (Fin 781) (ZMod 3),
    (∀ k < 11, ((x k : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      CFSG.KD.Fi24Img.img k) ∧ (∀ k, 11 ≤ k → x k = 1) ∧
    (∀ v ∈ TauCeti.Sporadic.fi24PrimePresentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd x v = 1) ∧
    (∀ g : GL (Fin 781) (ZMod 3), g.val = CFSG.Sporadic.Fi24.mA ∨ g.val = CFSG.Sporadic.Fi24.mB →
      g ∈ Subgroup.closure (x '' Set.Iio 11)) ∧
    (∀ k, k < 8 ∨ k = 9 → x k ∈ stab V0) ∧
    act (CFSG.Sporadic.Bridge.wordProd x pv) (CFSG.Sporadic.Fi24.pt 0).sp = V0 ∧
    (((x 7 * x 10 : GL (Fin 781) (ZMod 3))) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      CFSG.Sporadic.Fi24.mA := by
  obtain ⟨x, hx, h1, hrel, hcl⟩ := CertificateChecks.KernelSpor.Fi24Img.bridge_x
  have hxR : ∀ g < 11, (x g).val = mat3 781 609961 (RB (g + 1)) := fun g hg =>
    (hx g hg).trans (CertificateChecks.KernelSpor.Fi24Img.img_eq g hg)
  refine ⟨x, hx, h1, hrel, hcl, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < 11 := by omega
    have hc := canon_letM (l := (k, true)) hk'
    refine keeps_stab hc (hxR k hk') ?_
    rcases hk with hk | rfl
    · interval_cases k
      · exact keeps0
      · exact keeps1
      · exact keeps2
      · exact keeps3
      · exact keeps4
      · exact keeps5
      · exact keeps6
      · exact keeps7
    · exact keeps9
  · have hR : Canon3 609961 R := canon_of_vld (andB_true3 valid).1
    have hW := (wordMul_mat hR pv pv_lt).2
    rw [pv_regs, Nat.eq_of_beq_eq_true chain] at hW
    have hval := val_wordProd hs hroot hinv hxR pv_lt
    have hY : LinearMap.range (mat3 781 609961 Y).mulVecLin = V0 := by
      have hYc : Canon3 609961 Y := canon_of_vld (andB_true3 (andB_true3 valid).2).1
      have hQ : Canon3 609961 Q := canon_of_vld (andB_true3 (andB_true3 (andB_true3 valid).2).2).1
      have hCc : Canon3 609961 C := canon_of_vld (andB_true3 (andB_true3 (andB_true3 valid).2).2).2
      obtain ⟨-, e1⟩ := hs.mul_sound _ _ hQ hYc
      obtain ⟨-, e2⟩ := hs.mul_sound _ _ hYc hCc
      rw [Nat.eq_of_beq_eq_true span_le] at e1
      rw [Nat.eq_of_beq_eq_true span_ge] at e2
      change _ = LinearMap.range (mat3 781 609961 Q).mulVecLin
      apply le_antisymm
      · exact range_le_of_mul_eq e1.symm
      · rw [e2, range_mul]
        exact LinearMap.map_le_range
    rw [← hY, hW, range_mul, root_eq]
    unfold act
    rw [hval]
  · have h7 := canon_letM (l := (7, true)) (by norm_num)
    have h10 := canon_letM (l := (10, true)) (by norm_num)
    obtain ⟨-, e⟩ := hs.mul_sound _ _ h7 h10
    change mat3 781 609961 (MUL (RB 8) (RB 11)) = mat3 781 609961 (RB 8) * mat3 781 609961 (RB 11) at e
    rw [Nat.eq_of_beq_eq_true mA_regs] at e
    rw [Units.val_mul, hxR 7 (by norm_num), hxR 10 (by norm_num), CFSG.Sporadic.Fi24.mA,
      mA_eq]
    exact e.symm

end CertificateChecks.KernelFi24Fix

end
