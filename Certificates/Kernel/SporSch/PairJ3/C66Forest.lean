module

public import Certificates.Kernel.SporSch.PairJ3.C66In0
public import Certificates.Kernel.SporSch.PairJ3.C66In1
public import Certificates.Kernel.SporSch.PairJ3.C66Out0
public import Certificates.Kernel.SporSch.PairJ3.C66Out1
public import Certificates.Kernel.SporSch.PairJ3.C81Facts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 400000

#kss_b2all CertificateChecks.KernelSporSch.PJ3C66 CertificateChecks.KernelSporSch.PJ3C66.fiB 8 6
#kss_b2all CertificateChecks.KernelSporSch.PJ3C66 CertificateChecks.KernelSporSch.PJ3C66.foB 6 6

namespace CertificateChecks.KernelSporSch.PJ3C66

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CertificateChecks.KernelSporSch.PJ3C81
open CFSG.Sporadic.SmallOddCore Subgroup

theorem keyL_eqOn {n : Nat} {f g : Nat → Nat} : ∀ {bs : List Nat},
    (∀ b ∈ bs, f b < n ∧ g b < n) → keyL n f bs = keyL n g bs → ∀ b ∈ bs, f b = g b
  | [], _, _ => fun _ hb => absurd hb List.not_mem_nil
  | b :: bs, hlt, h => by
    have h' : f b + n * keyL n f bs = g b + n * keyL n g bs := by
      have e1 : keyL n f (b :: bs) = f b + n * keyL n f bs := by
        change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) = _
        exact strictN_val _ _
      have e2 : keyL n g (b :: bs) = g b + n * keyL n g bs := by
        change strictN (keyL n g bs) (fun r => Nat.add (g b) (Nat.mul n r)) = _
        exact strictN_val _ _
      rw [← e1, ← e2]
      exact h
    obtain ⟨hf, hg⟩ := hlt b List.mem_cons_self
    have hb : f b = g b := by
      have := congrArg (· % n) h'
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hg] at this
      exact this
    have hrest : keyL n f bs = keyL n g bs := by
      rw [hb] at h'
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h')
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hb
    · exact keyL_eqOn (fun c hc => hlt c (List.mem_cons_of_mem _ hc)) hrest c hc

theorem ltB {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

section J3


theorem eqOfKeyF {f g : Nat → Nat} {x y : Equiv.Perm (Fin 6156)} (hf : RepF 6156 f x)
    (hg : RepF 6156 g y) (hxy : y⁻¹ * x ∈ P3) (h : keyL 6156 f bs = keyL 6156 g bs) : x = y := by
  have hon := keyL_eqOn (fun b hb => ⟨hf.lt (hbs b hb), hg.lt (hbs b hb)⟩) h
  have h1 := hH (y⁻¹ * x) hxy fun z hz => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    refine Fin.ext ?_
    rw [← hf z z.2, ← hg z z.2]
    exact hon z hz
  exact (inv_mul_eq_one.1 h1).symm

theorem fAtG_spec {r N ng nr : Nat} {s : Nat → Nat → Nat} {K P G D R : Nat → Nat} {j : Nat}
    (hj : j < N) (h : fAtG r N ng nr s K P G D R j = true) :
    (D j = 0 ∧ P j < nr ∧ R (P j) = j) ∨
      (P j < N ∧ G j < ng ∧ D j = D (P j) + 1 ∧ cKey r (G j) (s (P j)) = K j) := by
  unfold fAtG at h
  rw [blt_true hj] at h
  by_cases hD : D j = 0
  · have e : Nat.beq (D j) 0 = true := by rw [hD]; rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    exact Or.inl ⟨hD, ltB h1, Nat.eq_of_beq_eq_true h2⟩
  · have e : Nat.beq (D j) 0 = false := by
      cases h' : Nat.beq (D j) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') hD
    rw [e] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
    exact Or.inr ⟨ltB h1, ltB h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem fiRow {j : Nat} (hj : j < 26163) : fiAt j = true := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (j / 3420) 6) (j / 570 % 6)) 570) fiAt 570 = true :=
    fiB_all (j / 3420) (by omega : j / 3420 < 8) (j / 570 % 6) (by omega : j / 570 % 6 < 6)
  have h := allBlk_spec h0 (j % 570) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (j / 3420) 6) (j / 570 % 6)) 570) (j % 570) = j := by
    change (j / 3420 * 6 + j / 570 % 6) * 570 + j % 570 = j
    omega
  rwa [e] at h

theorem foRow {j : Nat} (hj : j < 20520) : foAt j = true := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (j / 3420) 6) (j / 570 % 6)) 570) foAt 570 = true :=
    foB_all (j / 3420) (by omega : j / 3420 < 6) (j / 570 % 6) (by omega : j / 570 % 6 < 6)
  have h := allBlk_spec h0 (j % 570) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (j / 3420) 6) (j / 570 % 6)) 570) (j % 570) = j := by
    change (j / 3420 * 6 + j / 570 % 6) * 570 + j % 570 = j
    omega
  rwa [e] at h

theorem sI_rep {j : Nat} (hj : j < 26163) : RepF 6156 (sI j) (xE j) := E_rep (inv_rec hj).1

theorem conj_rep {r g B : Nat} (hB : gBase r = B) (hk : B + g < 31) {s : Nat → Nat}
    {x : Equiv.Perm (Fin 6156)} (hs : RepF 6156 s x) :
    RepF 6156 (fun b => hP r g (s (hI r g b))) (Tb (B + g) * x * (Tb (B + g))⁻¹) := by
  have e1 : ∀ y, hP r g y = cP (B + g) y := fun y => by
    unfold hP
    rw [hB]
    rfl
  have e2 : ∀ y, hI r g y = cI (B + g) y := fun y => by
    unfold hI
    rw [hB]
    rfl
  intro y hy
  change hP r g (s (hI r g y)) = _
  rw [e1, e2]
  exact (((rep_T hk).1.comp (hs.comp (rep_T hk).2)).congr (by group)) y hy

theorem forestI : ∀ d j, C66D.FID j = d → j < 26163 →
    ∃ k < 27, ∃ c ∈ K1, xE j = c * xE (C66D.RI k) * c⁻¹ := by
  intro d
  induction d with
  | zero =>
    intro j hd hj
    rcases fAtG_spec hj (fiRow hj) with ⟨-, hk, hR⟩ | ⟨-, -, hdd, -⟩
    · exact ⟨_, hk, 1, K1.one_mem, by rw [hR, one_mul, inv_one, mul_one]⟩
    · omega
  | succ d ih =>
    intro j hd hj
    rcases fAtG_spec hj (fiRow hj) with ⟨h0, -⟩ | ⟨hp, hg, hdd, hkey⟩
    · omega
    obtain ⟨k, hk, c, hc, he⟩ := ih (C66D.FIP j) (by omega) hp
    have hx : Tb (10 + C66D.FIG j) * xE (C66D.FIP j) * (Tb (10 + C66D.FIG j))⁻¹ = xE j := by
      refine eqOfKeyF (conj_rep (r := 0) (B := 10) rfl (by omega) (sI_rep hp)) (sI_rep hj) ?_ ?_
      · have hT := g1_P (j := C66D.FIG j) hg
        exact P3.mul_mem (P3.inv_mem (xE_mem hj))
          (P3.mul_mem (P3.mul_mem hT (xE_mem hp)) (P3.inv_mem hT))
      · exact hkey.trans (key_rec hj)
    refine ⟨k, hk, Tb (10 + C66D.FIG j) * c, K1.mul_mem (g1_K hg) hc, ?_⟩
    rw [← hx, he]
    group

noncomputable abbrev sOE (j : Nat) : Equiv.Perm (Fin 6156) :=
  E (C81D.CL j) * Tb 21 * (E (C81D.CL j))⁻¹

theorem sO_rep {j : Nat} (hj : j < 20520) : RepF 6156 (sO j) (sOE j) := conjE_rep (clRow hj).1

theorem tpt_mem {p : Equiv.Perm (Fin 6156)} (hp : p ∈ P3) : Tb 21 * p * Tb 21 ∈ P3 := by
  have h := P3.mul_mem (P3.mul_mem T21U (conjU_mem hp)) (P3.inv_mem T21U)
  have e : Tb 21 * U * (U * p * U) * (Tb 21 * U)⁻¹ = Tb 21 * p * Tb 21 := by
    rw [mul_inv_rev, Uinv, T21inv]
    simp only [mul_assoc, UU]
  rwa [e] at h

theorem outer_mem {a b : Equiv.Perm (Fin 6156)} (ha : a ∈ P3) (hb : b ∈ P3) :
    (b * Tb 21 * b⁻¹)⁻¹ * (a * Tb 21 * a⁻¹) ∈ P3 := by
  have e : (b * Tb 21 * b⁻¹)⁻¹ * (a * Tb 21 * a⁻¹) = b * (Tb 21 * (b⁻¹ * a) * Tb 21) * a⁻¹ := by
    rw [show (b * Tb 21 * b⁻¹)⁻¹ = b * (Tb 21)⁻¹ * b⁻¹ by group, T21inv]
    group
  rw [e]
  exact P3.mul_mem (P3.mul_mem hb (tpt_mem (P3.mul_mem (P3.inv_mem hb) ha))) (P3.inv_mem ha)

theorem forestO : ∀ d j, C66D.FOD j = d → j < 20520 →
    ∃ k < 22, ∃ c ∈ K2, sOE j = c * sOE (C66D.RO k) * c⁻¹ := by
  intro d
  induction d with
  | zero =>
    intro j hd hj
    rcases fAtG_spec hj (foRow hj) with ⟨-, hk, hR⟩ | ⟨-, -, hdd, -⟩
    · exact ⟨_, hk, 1, K2.one_mem, by rw [hR, one_mul, inv_one, mul_one]⟩
    · omega
  | succ d ih =>
    intro j hd hj
    rcases fAtG_spec hj (foRow hj) with ⟨h0, -⟩ | ⟨hp, hg, hdd, hkey⟩
    · omega
    obtain ⟨k, hk, c, hc, he⟩ := ih (C66D.FOP j) (by omega) hp
    have hT := g2_P (j := C66D.FOG j) hg
    have hEp := E_mem (clRow hp).1
    have hEj := E_mem (clRow hj).1
    have hx : Tb (22 + C66D.FOG j) * sOE (C66D.FOP j) * (Tb (22 + C66D.FOG j))⁻¹ = sOE j := by
      refine eqOfKeyF (conj_rep (r := 1) (B := 22) rfl (by omega) (sO_rep hp)) (sO_rep hj) ?_ ?_
      · have e : Tb (22 + C66D.FOG j) * sOE (C66D.FOP j) * (Tb (22 + C66D.FOG j))⁻¹ =
            (Tb (22 + C66D.FOG j) * E (C81D.CL (C66D.FOP j))) * Tb 21 *
              (Tb (22 + C66D.FOG j) * E (C81D.CL (C66D.FOP j)))⁻¹ := by group
        rw [e]
        exact outer_mem (P3.mul_mem hT hEp) hEj
      · exact hkey.trans (clRow hj).2.1.symm
    refine ⟨k, hk, Tb (22 + C66D.FOG j) * c, K2.mul_mem (g2_K hg) hc, ?_⟩
    rw [← hx, he]
    group

theorem cl_cover {s : Equiv.Perm (Fin 6156)} (hs : s ∈ conjClass j3P (Tb 21)) :
    ∃ j < 20520, sOE j = s := by
  let f : Fin 20520 → Equiv.Perm (Fin 6156) := fun i => sOE i
  have hf : Function.Injective f := by
    intro a b hab
    have hk : clKey (C81D.CL a) = clKey (C81D.CL b) := keyL_congr 6156 fun x hx =>
      ((conjE_rep (clRow a.2).1) x (hbs x hx)).trans
        ((congrArg (fun g : Equiv.Perm (Fin 6156) => (g ⟨x, hbs x hx⟩ : ℕ)) hab).trans
          ((conjE_rep (clRow b.2).1) x (hbs x hx)).symm)
    rw [(clRow a.2).2.1, (clRow b.2).2.1] at hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact (CK_mono _ _ h b.2).ne hk
    · exact (CK_mono _ _ h a.2).ne' hk
  have hsub : Set.range f ⊆ conjClass j3P (Tb 21) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨E (C81D.CL i), P_eq3 ▸ E_mem (clRow i.2).1, rfl⟩
  have hcard : (conjClass j3P (Tb 21)).ncard ≤ (Set.range f).ncard := by
    rw [row2.2.2.2.2.2.1, Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  rw [← heq] at hs
  obtain ⟨i, rfl⟩ := hs
  exact ⟨i, i.2, rfl⟩

end J3

end CertificateChecks.KernelSporSch.PJ3C66

end
