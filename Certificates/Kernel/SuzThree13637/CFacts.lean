module

public import Certificates.Kernel.SuzThree13637.BindFacts
public import Certificates.Kernel.SuzThree13637.CCls
public import CFSG.Certificates.Kernel.Spor.ClsKSound
public import CFSG.Certificates.Kernel.Spor.PSearchSound
public import CFSG.Sporadic.SuzOddCore.SmallChain
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PSearch CFSG.KS.ClsK
  CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor CFSG.Certificates
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.RankThree.Native
  CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (permOfArr)

theorem c_size : (cGens (levels ())).size = 3 := c_gen.1.trans ce_n'.2

theorem c_get {k : ℕ} (hk : k < 3) : (cGens (levels ()))[k]! = unpack 1782 11 (CE.G k) :=
  c_gen.2 k (by rw [ce_n'.2]; exact hk)

theorem prep_G {k : ℕ} (hk : k < 3) :
    PRep 1782 11 (CE.G k) (permOfArr 1782 (unpack 1782 11 (CE.G k))) :=
  prep_of_rep (rep_of_validA (validA_of (ce_reb' hk).2.2))

theorem cd_parts : CD.I = pidn 1782 11 ∧ CD.Y = CE.G 0 ∧
    pcomp 1782 11 (mask 11) CD.Y CD.Y = CD.Y2 := by
  have h := cd_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

@[expose] noncomputable def yP : Equiv.Perm (Fin 1782) := permOfArr 1782 (yArr (levels ()))

theorem prep_Y : PRep 1782 11 CD.Y yP := by
  have e0 : unpack 1782 11 (CE.G 0) = yArr (levels ()) := (c_get (by norm_num)).symm.trans rfl
  have h := prep_G (k := 0) (by norm_num)
  rw [e0] at h
  rw [cd_parts.2.1]
  exact h

theorem prep_I : PRep 1782 11 CD.I 1 := by
  rw [cd_parts.1]
  exact prep_pidn (by norm_num) (by norm_num)

theorem prep_Y2 : PRep 1782 11 CD.Y2 (yP * yP) := by
  rw [← cd_parts.2.2]
  exact prep_pcomp (by norm_num) prep_Y prep_Y

@[expose] def levOf (a b c : Equiv.Perm (Fin 1782)) : ℕ → Equiv.Perm (Fin 1782)
  | 1 => a
  | 2 => b
  | 4 => c
  | _ => 1

@[expose] noncomputable def yLev : ℕ → Equiv.Perm (Fin 1782) := levOf yP yP (yP * yP)

theorem levOf_one (a b c : Equiv.Perm (Fin 1782)) : levOf a b c 1 = a := rfl

theorem levOf_two (a b c : Equiv.Perm (Fin 1782)) : levOf a b c 2 = b := rfl

theorem levOf_four (a b c : Equiv.Perm (Fin 1782)) : levOf a b c 4 = c := rfl

theorem levOf_other (a b c : Equiv.Perm (Fin 1782)) {l : ℕ} (h1 : l ≠ 1) (h2 : l ≠ 2)
    (h4 : l ≠ 4) : levOf a b c l = 1 := by
  unfold levOf
  split <;> simp_all

theorem yLev_one : yLev 1 = yP := by rw [yLev, levOf_one]

theorem yLev_two : yLev 2 = yP := by rw [yLev, levOf_two]

theorem yLev_four : yLev 4 = yP * yP := by rw [yLev, levOf_four]

theorem yLev_other {l : ℕ} (h1 : l ≠ 1) (h2 : l ≠ 2) (h4 : l ≠ 4) : yLev l = 1 := by
  rw [yLev, levOf_other _ _ _ h1 h2 h4]

theorem nthN_cons_zero (x : ℕ) (L : List ℕ) : nthN (x :: L) 0 = x := rfl

theorem nthN_cons_succ (x : ℕ) (L : List ℕ) (i : ℕ) : nthN (x :: L) (i + 1) = nthN L i := rfl

theorem prep_lev : ∀ l < 6, PRep 1782 11 (nthN yYs l) (yLev l) := by
  intro l hl
  rw [yYs]
  interval_cases l
  · rw [nthN_cons_zero, yLev_other (by omega) (by omega) (by omega)]
    exact prep_I
  · rw [nthN_cons_succ, nthN_cons_zero, yLev_one]
    exact prep_Y
  · rw [nthN_cons_succ, nthN_cons_succ, nthN_cons_zero, yLev_two]
    exact prep_Y
  · rw [nthN_cons_succ, nthN_cons_succ, nthN_cons_succ, nthN_cons_zero,
      yLev_other (by omega) (by omega) (by omega)]
    exact prep_I
  · rw [nthN_cons_succ, nthN_cons_succ, nthN_cons_succ, nthN_cons_succ, nthN_cons_zero,
      yLev_four]
    exact prep_Y2
  · rw [nthN_cons_succ, nthN_cons_succ, nthN_cons_succ, nthN_cons_succ, nthN_cons_succ,
      nthN_cons_zero, yLev_other (by omega) (by omega) (by omega)]
    exact prep_I

theorem strictB_eq13637 (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem gen_mem {k : ℕ}
    (hk : k < 3) : permOfArr 1782 (unpack 1782 11 (CE.G k)) ∈
      Subgroup.centralizer ({yP} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM := by
  have h := cgen_ok k hk
  unfold cgenOK at h
  rw [strictB_eq13637, bAnd_eqS, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hG := prep_G hk
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · refine Equiv.ext fun x => Fin.ext ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec h1 x x.2)
    rw [prep_Y x, hG (yP x), hG x, prep_Y (permOfArr 1782 (unpack 1782 11 (CE.G k)) x)] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact e
  · apply (mem_suzM_iff_siftA (rep_of_validA (validA_of (ce_reb' hk).2.2))).1
    rw [smallLevels]
    exact siftA_of Suz2306.binds Suz2306.perm SuzC.hl ⟨h2, h3, h4⟩

theorem cKeys_lt13637 : ∀ q ∈ cKeys, q < 1782 := by decide

theorem c_card : Nat.card (Subgroup.closure (permsA 1782 (cGens (levels ())))) = 3240 :=
  (enumOK_spec cKeys_lt13637 c_enum.1).2.1.trans c_enum.2.1

theorem c_cent :
    Subgroup.closure (permsA 1782 (cGens (levels ()))) =
      Subgroup.centralizer ({yP} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM := by
  set K := Subgroup.centralizer ({yP} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM
  have hCK : Subgroup.closure (permsA 1782 (cGens (levels ()))) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk3 : k < 3 := by rw [← c_size]; exact hk
    dsimp only
    rw [c_get hk3]
    exact gen_mem hk3
  have hcy : ∀ c ∈ K, Commute c yP := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).1
  have hK : K ≤ smallChain.originalSubgroup := by
    rw [smallChain_originalSubgroup]
    exact inf_le_right
  have hKY : ∀ c ∈ K, ∀ l < 6, c * yLev l = yLev l * c := by
    intro c hc l hl
    have h := hcy c hc
    interval_cases l
    · rw [yLev_other (by omega) (by omega) (by omega)]
      exact (Commute.one_right c).eq
    · rw [yLev_one]
      exact h.eq
    · rw [yLev_two]
      exact h.eq
    · rw [yLev_other (by omega) (by omega) (by omega)]
      exact (Commute.one_right c).eq
    · rw [yLev_four]
      exact (h.mul_right h).eq
    · rw [yLev_other (by omega) (by omega) (by omega)]
      exact (Commute.one_right c).eq
  have hKpr : ∀ P ∈ [CD.Y], ∃ g : Equiv.Perm (Fin 1782), PRep 1782 11 P g ∧
      ∀ c ∈ K, c * g = g * c := by
    intro P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact ⟨yP, prep_Y, fun c hc => (hcy c hc).eq⟩
  have hcnt := natCard_le_pcnt smallChain_arrays (chainCheckFacts smallChain_check.1)
    smallChain_valid Suz2306.binds Suz2306.perm SuzC.hl csrc_ok prep_lev hK hKY hKpr
  rw [Nat.eq_of_beq_eq_true csearch_ok] at hcnt
  exact Subgroup.eq_of_le_of_card_ge hCK (by rw [c_card]; exact hcnt)

theorem c_class {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ Subgroup.closure (permsA 1782 (cGens (levels ())))) (hg1 : g ≠ 1)
    (hg25 : g ^ 2 = 1 ∨ g ^ 5 = 1) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 1782))) ⊓
      Subgroup.closure (permsA 1782 (cGens (levels ())))) < 81 := by
  obtain ⟨hmemC, hcardC, hval⟩ := enumOK_spec cKeys_lt13637 c_enum.1
  obtain ⟨-, hsz, hpts⟩ := c_enum
  have hX : ∀ i < 3240, PRep 1782 11 (CE.T i) (permOfArr 1782 (unpack 1782 11 (CE.T i))) := by
    intro i hi
    have h := rep_of_validA (hval i (by rw [hsz]; exact hi))
    rw [hpts i hi] at h
    exact prep_of_rep h
  have hmem : ∀ i < 3240, permOfArr 1782 (unpack 1782 11 (CE.T i)) ∈
      Subgroup.closure (permsA 1782 (cGens (levels ()))) := fun i hi =>
    (hmemC _).2 ⟨i, by rw [hsz]; exact hi, by rw [hpts i hi]⟩
  have hall : ∀ x ∈ Subgroup.closure (permsA 1782 (cGens (levels ()))),
      ∃ i < 3240, permOfArr 1782 (unpack 1782 11 (CE.T i)) = x := by
    intro x hx
    obtain ⟨i, hi, e⟩ := (hmemC x).1 hx
    rw [hsz] at hi
    exact ⟨i, hi, by rw [← e, hpts i hi]⟩
  have h := card_mul_le_of_clsK hX hmem hall (hcardC.trans hsz) prep_I (by decide) cls_ok hg hg1
    hg25
  omega

end CFSG.KD.SuzThree13637

end
