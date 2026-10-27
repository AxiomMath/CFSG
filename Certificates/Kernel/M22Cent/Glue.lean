module

public import Certificates.Data.Kernel.M22Cent.Defs
public import CFSG.Sporadic.Schreier.M22
import Certificates.Kernel.M22Cent.Checks

public section

namespace CertificateChecks.KernelM22Cent

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  Certificates.Kernel.M22Cent CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.Certificates

def Pres (f : Fin 22 → Fin 22) : Prop := ∀ B ∈ hexads, ∃ B' ∈ hexads, ∀ i ∈ B, f i ∈ B'

theorem pres_of_presB {f : Fin 22 → Fin 22} (h : presB f = true) : Pres f := by
  simpa [presB, Pres] using h

theorem pres_comp {f g : Fin 22 → Fin 22} (hf : Pres f) (hg : Pres g) :
    Pres fun i => f (g i) := by
  intro B hB
  obtain ⟨B', hB', h1⟩ := hg B hB
  obtain ⟨B'', hB'', h2⟩ := hf B' hB'
  exact ⟨B'', hB'', fun i hi => h2 _ (h1 i hi)⟩

theorem pres_id : Pres fun i => i := fun B hB => ⟨B, hB, fun _ hi => hi⟩

theorem pres_pw {b : Bool} {f r : Fin 22 → Fin 22} (hf : Pres f) (hr : Pres r) :
    Pres fun i => pw b f (r i) := by
  cases b
  · exact hr
  · exact pres_comp hf hr

theorem pres_xf (k : Nat) (hk : k < 4) : Pres (xf k) := by
  have h := pres_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact pres_of_presB (h.1 k hk)

theorem pres_fe (e : Nat) : Pres (fe e) :=
  pres_pw (pres_xf 0 (by decide)) (pres_pw (pres_xf 1 (by decide))
    (pres_pw (pres_xf 2 (by decide)) (pres_pw (pres_xf 3 (by decide)) pres_id)))

theorem pres_beta : Pres (tf betaTab) := by
  have h := pres_ok
  simp only [Bool.and_eq_true] at h
  exact pres_of_presB h.2

theorem m22_pres {σ : Equiv.Perm (Fin 22)} (hσ : σ ∈ NativeSporadic.M22) : Pres σ := by
  rw [m22_eq, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hσ
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rcases hx with rfl | rfl
      · exact pres_of_presB (by decide +kernel)
      · exact pres_of_presB (by decide +kernel)
    · rw [Set.mem_inv] at hx
      rcases hx with hx | hx
      · rw [← inv_inv x, hx]
        exact pres_of_presB (by decide +kernel)
      · rw [← inv_inv x, hx]
        exact pres_of_presB (by decide +kernel)
  | one => exact pres_id
  | mul x y _ _ hx hy => exact pres_comp (f := x) (g := y) hx hy

theorem m22_even {σ : Equiv.Perm (Fin 22)} (hσ : σ ∈ NativeSporadic.M22) :
    Equiv.Perm.sign σ = 1 := by
  have h : NativeSporadic.M22 ≤ alternatingGroup (Fin 22) := by
    rw [m22_eq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)
  exact Equiv.Perm.mem_alternatingGroup.1 (h hσ)

theorem fe_invol (e : Nat) (he : e < 16) (j : Fin 22) : fe e (fe e j) = j := by
  have h := fe_inv
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h e he j

theorem beta_invol (j : Fin 22) : tf betaTab (tf betaTab j) = j := by
  have h := beta_inv
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h j

def fP (e : Fin 16) : Equiv.Perm (Fin 22) :=
  ⟨fe e.val, fe e.val, fe_invol e.val e.isLt, fe_invol e.val e.isLt⟩

def bP : Equiv.Perm (Fin 22) := ⟨tf betaTab, tf betaTab, beta_invol, beta_invol⟩

theorem sign_ok : ∀ e : Fin 16, Equiv.Perm.sign (fP e * bP) = -1 := by
  decide +kernel

theorem conjAt_imp {y : Equiv.Perm (Fin 22)} {x x' : Tab} (h : conjAt y x x' = true) (i : Fin 22) :
    y (tf x' i) = tf x (y i) := by
  simp only [conjAt, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  apply Fin.ext
  simp only [tf]
  rw [Fin.val_ofNat, ← h i, Nat.mod_eq_of_lt (Fin.isLt _)]

theorem comm_fe (u : Fin 22 → Fin 22) (hu : ∀ k : Fin 4, ∀ j, u (xf k.val j) = xf k.val (u j))
    (e : Nat) (j : Fin 22) : u (fe e j) = fe e (u j) := by
  have h0 : ∀ j, u (xf 0 j) = xf 0 (u j) := hu ⟨0, by decide⟩
  have h1 : ∀ j, u (xf 1 j) = xf 1 (u j) := hu ⟨1, by decide⟩
  have h2 : ∀ j, u (xf 2 j) = xf 2 (u j) := hu ⟨2, by decide⟩
  have h3 : ∀ j, u (xf 3 j) = xf 3 (u j) := hu ⟨3, by decide⟩
  simp only [fe, pw]
  split_ifs <;> simp only [h0, h1, h2, h3]

theorem no_cent (y : Equiv.Perm (Fin 22)) (hy : y ∈ NativeSporadic.M22)
    (hc : ∀ k : Fin 4, ∀ i, y (tf (centConj (xsL.getD k.val [])) i) = xf k.val (y i)) : False := by
  have hconj : ∀ k : Fin 4, ∀ j,
      tf (centConj (xsL.getD k.val [])) (tf betaTab j) = tf betaTab (xf k.val j) := by
    have h := conj_ok
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
    exact h
  have hxc : ∀ k l : Fin 4, ∀ j, xf k.val (xf l.val j) = xf l.val (xf k.val j) := by
    have h := xf_comm
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
    exact h
  have horb : ∀ q, mv q = true → ∃ e < 16, fe e 0 = q := by
    intro q hq
    have h := List.all_eq_true.1 orbit_ok q (List.mem_finRange q)
    rw [hq, Bool.not_true, Bool.false_or, List.any_eq_true] at h
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, List.mem_range.1 he, beq_iff_eq.1 h⟩
  let g : Fin 22 → Fin 22 := fun i => y (tf betaTab i)
  have hgx : ∀ k : Fin 4, ∀ j, g (xf k.val j) = xf k.val (g j) := by
    intro k j
    change y (tf betaTab (xf k.val j)) = xf k.val (y (tf betaTab j))
    rw [← hconj k j, hc k]
  have hginj : Function.Injective g := by
    intro a b hab
    have h := congrArg (tf betaTab) (y.injective hab)
    rwa [beta_invol, beta_invol] at h
  have hfec : ∀ e e' j, fe e (fe e' j) = fe e' (fe e j) := by
    intro e e' j
    have h : ∀ k : Fin 4, ∀ j, fe e (xf k.val j) = xf k.val (fe e j) :=
      fun k j => (comm_fe (xf k.val) (fun l j => hxc k l j) e j).symm
    exact comm_fe (fe e) h e' j
  have hmv0 : mv (g 0) = true := by
    have h0 := mv_zero
    simp only [mv, bne_iff_ne, ne_eq] at h0 ⊢
    intro h
    exact h0 (hginj ((hgx ⟨0, by decide⟩ 0).trans h))
  obtain ⟨e, he, hfe0⟩ := horb _ hmv0
  have hcomp : ∀ p, mv p = true → g p = fe e p := by
    intro p hp
    obtain ⟨e', -, rfl⟩ := horb p hp
    rw [comm_fe g hgx, ← hfe0, hfec]
  let h : Fin 22 → Fin 22 := fun i => fe e (g i)
  have hfix : ∀ p, mv p = true → h p = p := fun p hp => by
    change fe e (g p) = p
    rw [hcomp p hp, fe_invol e he]
  have hinj : Function.Injective h := by
    intro a b hab
    have h1 := congrArg (fe e) hab
    change fe e (fe e (g a)) = fe e (fe e (g b)) at h1
    rw [fe_invol e he, fe_invol e he] at h1
    exact hginj h1
  have hpres : Pres h := pres_comp (pres_fe e) (pres_comp (m22_pres hy) pres_beta)
  have key : ∀ B ∈ hexads, uniqB B = true → ∀ i ∈ B, h i ∈ B := by
    intro B hB hu i hi
    obtain ⟨B', hB', himg⟩ := hpres B hB
    have hu' := List.all_eq_true.1 hu B' hB'
    have hBB : B' = B := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu'
      rcases hu' with hu' | hu'
      · exfalso
        rw [Bool.eq_false_iff] at hu'
        apply hu'
        rw [List.all_eq_true]
        intro c hc
        rw [Bool.or_eq_true]
        by_cases hmc : mv c = true
        · right
          have h1 := himg c hc
          rw [hfix c hmc] at h1
          exact List.elem_iff.2 h1
        · left
          simpa using hmc
      · exact hu'
    rw [← hBB]
    exact himg i hi
  have hall : ∀ p, h p = p := by
    intro p
    by_cases hp : mv p = true
    · exact hfix p hp
    · have h1 := List.all_eq_true.1 wit_ok p (List.mem_finRange p)
      rw [Bool.not_eq_true] at hp
      rw [hp, Bool.false_or, List.any_eq_true] at h1
      obtain ⟨⟨p', B₁, B₂⟩, -, hw⟩ := h1
      simp only [Bool.and_eq_true, beq_iff_eq, witB] at hw
      obtain ⟨rfl, ⟨⟨⟨⟨⟨hB₁, hB₂⟩, hu₁⟩, hu₂⟩, hp₁⟩, hp₂⟩, hmeet⟩ := hw
      have q₁ := key B₁ (List.elem_iff.1 hB₁) hu₁ p' (List.elem_iff.1 hp₁)
      have q₂ := key B₂ (List.elem_iff.1 hB₂) hu₂ p' (List.elem_iff.1 hp₂)
      have h3 := List.all_eq_true.1 hmeet (h p') q₁
      have q₂' : B₂.contains (h p') = true := List.elem_iff.2 q₂
      rw [q₂'] at h3
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h3
      rcases h3 with h3 | h3
      · exact h3
      · exact hinj (hfix _ h3)
  have hy' : y = fP ⟨e, he⟩ * bP := by
    ext j
    have h1 := hall (tf betaTab j)
    change fe e (y (tf betaTab (tf betaTab j))) = tf betaTab j at h1
    rw [beta_invol] at h1
    change (y j : ℕ) = fe e (tf betaTab j)
    rw [← h1, fe_invol e he]
  have hs := m22_even hy
  rw [hy', sign_ok] at hs
  exact absurd hs (by decide)

theorem centOuterOK_true : centOuterOK = true := by
  rw [centOuterOK, List.all_eq_true]
  intro y hy
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have hyM : y ∈ NativeSporadic.M22 := by
    rw [← m22Certificate_originalSubgroup]
    exact (mem_enumeration_iff _ hQ y).1 hy
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hall
  rw [centXs_eq] at hall
  have hmem : ∀ k : Fin 4, xsL.getD k.val [] ∈ xsL := by
    decide +kernel
  exact no_cent y hyM fun k i => conjAt_imp (List.all_eq_true.1 hall _ (hmem k)) i

end CertificateChecks.KernelM22Cent
