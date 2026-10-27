module

public import Certificates.Kernel.Fi22Twist.PrChkX
public import Certificates.Kernel.Fi22Twist.PrChkC
public import Certificates.Kernel.Fi22Twist.PrChkV
public import Certificates.Kernel.Fi22Rank.Q2Facts
public import CFSG.Certificates.Kernel.Fi22Twist.PairSound
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.HardMathSupport.Foote.E27 CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw CFSG.RankThree.Native
open CertificateChecks.KernelFi22Rank.Q2
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative (qGens)

#kc_forall_tree pr431009xAll (fun q => ch431009px q = true) 46 CFSG.KD.Fi22Twist.ch431009px

#kc_forall_tree pr431009cAll (fun q => ch431009pc q = true) 92 CFSG.KD.Fi22Twist.ch431009pc

#kc_forall_tree pr431009vAll (fun q => ch431009pv q = true) 65 CFSG.KD.Fi22Twist.ch431009pv

theorem q2_tab : ∃ T : Subgroup (Equiv.Perm (Fin 3510)), ∃ e : ℕ → Equiv.Perm (Fin 3510),
    PairTab (MonoidHom.id _) e T KF PM PX PV ∧ T = Subgroup.closure (permsA 3510 (qGens 2)) := by
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
  have hx := blk_all (b := 16) (n := 729) (m := 46) (by norm_num) (by norm_num) pr431009xAll
  have P : PairTab (MonoidHom.id _) _ T KF PM PX PV :=
    { key := fun i hi => (hE i hi).2
      one := tabElt_zero _ _
      mem := hTmem
      xc := fun x h => ((bAnd_iff _ _).1 (hx x h)).1
      oc := fun x h => ((bAnd_iff _ _).1 (hx x h)).2
      cc := blk_all (b := 8) (n := 729) (m := 92) (by norm_num) (by norm_num) pr431009cAll
      vc := blk_all (b := 8) (n := 517) (m := 65) (by norm_num) (by norm_num) pr431009vAll }
  exact ⟨T, _, P, le_antisymm hTQ hQT⟩

theorem q2_e27_le_record (A : Subgroup (Equiv.Perm (Fin 3510)))
    (hA : A ≤ Subgroup.closure (permsA 3510 (qGens 2))) (hcard : Nat.card A = 27)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ c < 81, A ≤ Subgroup.closure {g | ∃ i < 729, qpBit (PM (730 + c)) i = true ∧
      PRep 3510 12 (MonoidHom.id _) (KF i) g} := by
  obtain ⟨T, e, P, hT⟩ := q2_tab
  obtain ⟨c, hc, hle⟩ := P.e27_le_record A (by rw [hT]; exact hA) hcard hcomm hexp
  refine ⟨c, hc, hle.trans (Subgroup.closure_mono ?_)⟩
  rintro _ ⟨i, hi, hbit, rfl⟩
  exact ⟨i, hi, hbit, P.key i hi⟩

end CertificateChecks.KernelFi22Twist

end
