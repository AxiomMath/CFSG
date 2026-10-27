module

public import Certificates.Kernel.Fi22Twist.DjChk
public import Certificates.Kernel.Fi22Twist.CjFacts
public import CFSG.Certificates.Kernel.Fi22Twist.DjSound
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.HardMathSupport.Foote.E27 CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw CFSG.RankThree.Native
open CertificateChecks.KernelFi22Rank.Q2
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative (qGens)

set_option maxRecDepth 400000

#kc_forall_tree dj431009All (fun j => ch431009dj_ j = true) 5
  CertificateChecks.KernelFi22Twist.ch431009dj_

theorem dSub_card {j : ℕ} (hj : j < 5) : Nat.card (dSub j) = 27 :=
  dj_card (DF := DF) (R := TX.F) (j := j)
    (fun z hz => ap_eq (rep_prep (k := 3 * j) (by omega)) hz)
    (fun z hz => ap_eq (rep_prep (k := 3 * j + 1) (by omega)) hz)
    (fun z hz => ap_eq (rep_prep (k := 3 * j + 2) (by omega)) hz)
    (df_mem hj) (dj431009All j hj)

theorem q2_card : Nat.card (Subgroup.closure (permsA 3510 (qGens 2))) = 729 := by
  obtain ⟨hsz, hget⟩ := CFSG.KC.Fi22RkS.rows_of (m := 3510) (K := 5) (w := 12) (by norm_num) szA
    rowsT
  have hPP : ∀ k < 5, PP 3510 12 (key (GI k)) := fun k hk => (hget k hk).2
  obtain ⟨g0, -, g2, g3, -⟩ := GI_vals
  have hgPP : ∀ j < 3, PP 3510 12 (gk j) := by
    intro j hj
    interval_cases j
    · have h := hPP 0 (by norm_num)
      rwa [key, g0] at h
    · have h := hPP 2 (by norm_num)
      rwa [key, g2] at h
    · have h := hPP 3 (by norm_num)
      rwa [key, g3] at h
  have hR := permRep (G := Equiv.Perm (Fin 3510)) (n := 3510) (w := 12) (by norm_num) (by norm_num)
    (ψ := MonoidHom.id _) Function.injective_id
  have hGs : ∀ x ∈ permsA 3510 (qGens 2), ∃ i < 729,
      PRep 3510 12 (MonoidHom.id _) (key i) x := by
    rintro x ⟨k, hk, rfl⟩
    have hk' : k < (qGens 2).size := hk
    rw [qGens_eq, hsz] at hk'
    refine ⟨GI k, ?_, ?_⟩
    · obtain ⟨e0, e1, e2, e3, e4⟩ := GI_vals
      interval_cases k <;> simp only [e0, e1, e2, e3, e4] <;> norm_num
    · beta_reduce
      rw [qGens_eq, (hget k hk').1]
      exact prep_of_PP (hPP k hk')
  have hb := blk_all (b := 16) (n := 729) (m := 46) (by norm_num) (by norm_num) treeAll
  have hg : ∀ j < 3, PRep 3510 12 (MonoidHom.id _) (gk j)
      (permOfArr 3510 (unpack 3510 12 (gk j))) := fun j hj => prep_of_PP (hgPP j hj)
  have ht := fun i hi => ((bAnd_iff _ _).1 (hb i hi)).1
  have hT := tabData_ofR (n := 729) (m := 3) hR hg ht
    (fun i hi j hj => allN_spec ((bAnd_iff _ _).1 (hb i hi)).2 j hj)
    (blk_all (by norm_num) (by norm_num : 729 ≤ 16 * 46) sortAll)
  have hE := tree_specR hR hg ht
  obtain ⟨T, hTmem, hTg⟩ := hT.exists_subgroup (by norm_num)
  have hQT : Subgroup.closure (permsA 3510 (qGens 2)) ≤ T := by
    refine (Subgroup.closure_le T).2 fun x hx => ?_
    obtain ⟨i, hi, hr⟩ := hGs x hx
    rw [← hR.elt (hE i hi).2 hr]
    exact (hTmem _).2 ⟨i, hi, rfl⟩
  have hTQ : T ≤ Subgroup.closure (permsA 3510 (qGens 2)) := by
    rw [hTg]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    have hq : ∀ k < 5, permOfArr 3510 (unpack 3510 12 (key (GI k))) ∈
        Subgroup.closure (permsA 3510 (qGens 2)) := by
      intro k hk
      refine Subgroup.subset_closure ⟨k, ?_, ?_⟩
      · change k < (qGens 2).size
        rw [qGens_eq, hsz]
        exact hk
      · beta_reduce
        rw [qGens_eq, (hget k hk).1]
    interval_cases j
    · have h := hq 0 (by norm_num)
      rwa [key, g0] at h
    · have h := hq 2 (by norm_num)
      rwa [key, g2] at h
    · have h := hq 3 (by norm_num)
      rwa [key, g3] at h
  rw [← le_antisymm hTQ hQT]
  exact hT.card_subgroup hTmem

end CertificateChecks.KernelFi22Twist

end
