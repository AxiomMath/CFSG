module

public import Certificates.Kernel.Y442.Model
public import Certificates.Kernel.Y442.St0
public import Certificates.Kernel.Y442.St1
public import CFSG.Certificates.Kernel.TwistDce.Sound

public section

namespace CertificateChecks.KernelY442

open CFSG.YGroups CFSG.YGroups.Y442Tw CFSG.KC CFSG.KC.YModel CFSG.KC.TwDce
  CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration

theorem sN_eq (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

section Fold
variable {F RD RW RA RJ : ℕ → ℕ} {THM E BS NB : ℕ}

theorem foldRange_succ (a n S : ℕ) : foldRange F THM E BS NB RD RW RA RJ a (n + 1) S =
    foldRange F THM E BS NB RD RW RA RJ (a + 1) n (foldStep F THM E BS NB RD RW RA RJ a S) :=
  sN_eq _ _

theorem foldRange_add (m : ℕ) : ∀ n a S, foldRange F THM E BS NB RD RW RA RJ a (n + m) S =
    foldRange F THM E BS NB RD RW RA RJ (a + n) m (foldRange F THM E BS NB RD RW RA RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    rw [show n + 1 + m = (n + m) + 1 by omega, foldRange_succ, foldRange_add m n (a + 1),
      foldRange_succ, show a + 1 + n = a + (n + 1) by omega]

theorem fold_cat {a n m S S₁ S₂ : ℕ} (h₁ : foldRange F THM E BS NB RD RW RA RJ a n S = S₁)
    (h₂ : foldRange F THM E BS NB RD RW RA RJ (a + n) m S₁ = S₂) :
    foldRange F THM E BS NB RD RW RA RJ a (n + m) S = S₂ := by
  rw [foldRange_add, h₁, h₂]

end Fold

@[expose] noncomputable def fd (a n S : ℕ) : ℕ :=
  foldRange CFSG.KD.YM432P.F CFSG.KD.Y442D.THM CFSG.KD.Y442D.E CFSG.KD.Y442D.BS
    CFSG.KD.Y442D.NB CFSG.KD.Y442D.RD CFSG.KD.Y442D.RW CFSG.KD.Y442D.RA CFSG.KD.Y442D.RJ a n S

theorem fd_cat {a n m b c S S₁ S₂ : ℕ} (h₁ : fd a n S = S₁) (h₂ : fd b m S₁ = S₂)
    (hb : a + n = b) (hc : n + m = c) : fd a c S = S₂ := by
  subst hb hc
  exact fold_cat h₁ h₂

theorem fd_of {a n S S' : ℕ} (h : Nat.beq (foldRange CFSG.KD.YM432P.F CFSG.KD.Y442D.THM
    CFSG.KD.Y442D.E CFSG.KD.Y442D.BS CFSG.KD.Y442D.NB CFSG.KD.Y442D.RD CFSG.KD.Y442D.RW
    CFSG.KD.Y442D.RA CFSG.KD.Y442D.RJ a n S) S' = true) : fd a n S = S' :=
  Nat.eq_of_beq_eq_true h

theorem fold_ok : fd 0 136 1 = 10 := by
  have c0 := fd_of CFSG.KD.Y442D.st0
  have c1 := fd_of CFSG.KD.Y442D.st1
  have c2 := fd_of CFSG.KD.Y442D.st2
  have c3 := fd_of CFSG.KD.Y442D.st3
  have c4 := fd_of CFSG.KD.Y442D.st4
  have c5 := fd_of CFSG.KD.Y442D.st5
  have c6 := fd_of CFSG.KD.Y442D.st6
  have c7 := fd_of CFSG.KD.Y442D.st7
  have c8 := fd_of CFSG.KD.Y442D.st8
  have c9 := fd_of CFSG.KD.Y442D.st9
  have c10 := fd_of CFSG.KD.Y442D.st10
  have c11 := fd_of CFSG.KD.Y442D.st11
  have d1 := fd_cat (c := nat_lit 24) c0 c1 rfl rfl
  have d2 := fd_cat (c := nat_lit 36) d1 c2 rfl rfl
  have d3 := fd_cat (c := nat_lit 48) d2 c3 rfl rfl
  have d4 := fd_cat (c := nat_lit 60) d3 c4 rfl rfl
  have d5 := fd_cat (c := nat_lit 72) d4 c5 rfl rfl
  have d6 := fd_cat (c := nat_lit 84) d5 c6 rfl rfl
  have d7 := fd_cat (c := nat_lit 96) d6 c7 rfl rfl
  have d8 := fd_cat (c := nat_lit 108) d7 c8 rfl rfl
  have d9 := fd_cat (c := nat_lit 120) d8 c9 rfl rfl
  have d10 := fd_cat (c := nat_lit 132) d9 c10 rfl rfl
  exact fd_cat (c := nat_lit 136) d10 c11 rfl rfl

theorem thm_spec : ∀ c < 10, thL CFSG.KD.Y442D.THM c < 10 →
    c ≠ 4 ∧ thL CFSG.KD.Y442D.THM c = th432 c := by
  decide +kernel

theorem e_eq : CFSG.KD.Y442D.E = 4 := by decide +kernel

theorem nb_eq : CFSG.KD.Y442D.NB = 10 := by decide +kernel

theorem bs_eq : ∀ i < 10, fld CFSG.KD.Y442D.BS (16 * i) 65535 = hPts.getD i 0 := by
  decide +kernel

section

@[expose] noncomputable def xL (c : ℕ) : Ghat swSp432_eq_one := psiG swSp432_eq_one (yGen 4 3 2 c)

theorem evalWord_xL (w : List ℕ) :
    evalWord xL w = psiG swSp432_eq_one (evalWord (yGen 4 3 2) w) := by
  rw [evalWord_map_hom]
  rfl

theorem facts : ∃ X : ℕ → Ghat swSp432_eq_one, X 0 = 1 ∧ ∀ r < 136,
    (dKind (CFSG.KD.Y442D.RD r) < 3 → dN1 (CFSG.KD.Y442D.RD r) < 10 ∧
      dN2 (CFSG.KD.Y442D.RD r) < 10 ∧
      X (dN1 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RW r) * u swSp432_eq_one *
        (X (dN2 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RA r))⁻¹ ∈
          (psiG swSp432_eq_one).range) ∧
    (3 ≤ dKind (CFSG.KD.Y442D.RD r) → dKind (CFSG.KD.Y442D.RD r) < 5 →
      dN2 (CFSG.KD.Y442D.RD r) < 10 ∧
      X (dN2 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RW r) *
        (X (dN2 (CFSG.KD.Y442D.RD r)))⁻¹ ∈ (psiG swSp432_eq_one).range) := by
  refine dce_sound fold_ok (by norm_num) (psiG swSp432_eq_one).range xL (u swSp432_eq_one)
    (fun c _ => ⟨_, rfl⟩) (fun c => by rw [xL, ← map_mul, yGen_mul_self, map_one])
    (u_mul_self _) ?_ ?_ ?_ ?_
  · intro c hc hth
    obtain ⟨h4, he⟩ := thm_spec c hc hth
    rw [he, xL, xL, u_conj _ hc h4]
  · intro _
    rw [e_eq]
    exact rel4 _
  · intro w hw he hb
    rw [evalWord_xL, evalWord_eq_one_of_base w hw he (fun m hm => by
      have := hb m (by rw [nb_eq]; exact hm)
      rwa [bs_eq m hm] at this), map_one]
  · decide +kernel

end

end CertificateChecks.KernelY442

end
