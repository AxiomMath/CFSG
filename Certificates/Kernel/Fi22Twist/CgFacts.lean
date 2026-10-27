module

public import Certificates.Kernel.Fi22Twist.L5Chk
public import Certificates.Kernel.Fi22Twist.SiftCUFacts
public import Certificates.Kernel.Sporadic.Fi22.Base6
public import CFSG.Certificates.Kernel.Fi22Twist.KeySound
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

set_option maxRecDepth 400000

#kc_forall_tree jx431009All (fun j => ch431009jx_ j = true) 5
  CertificateChecks.KernelFi22Twist.ch431009jx_

theorem cgIdx_lt {j m : ℕ} (hj : j < 5) (hm : m < t12 ngC j) : t12 gofC j + m < 23 := by
  have h : t12 gofC j + t12 ngC j ≤ 23 := by
    interval_cases j <;> decide
  omega

theorem jx_commK {j m : ℕ} (hj : j < 5) (hm : m < t12 ngC j) :
    commK CG DF (t12 gofC j) j m = true := by
  have h := jx431009All j hj
  unfold ch431009jx_ at h
  beta_reduce at h
  obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
  exact ((bAnd_iff _ _).1 (allBlk_spec0 h1 m hm)).1

theorem df_row {j : ℕ} (hj : j < 5) {t e : ℕ}
    (hte : (t = 0 ∧ e = 9) ∨ (t = 1 ∧ e = 3) ∨ (t = 2 ∧ e = 1)) :
    ∀ i < 3510, ap (DF (27 * j + e)) i = ap (rowR TX.F (3 * j + t)) i := by
  intro i hi
  have hz : ∀ k < 15, ap (rowR TX.F k) i < 3510 := fun k hk => by
    rw [ap_eq (rep_prep hk) hi]
    exact pt_lt _ _ hi
  have d0 := (dfK_sound (df_all hj (k := 0) (by norm_num))).1 rfl
  rcases hte with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := (dfK_sound (df_all hj (k := 9) (by norm_num))).2.2.2 (by norm_num) (by norm_num) i hi
    have e9 : 27 * j + 9 - 9 = 27 * j + 0 := by omega
    rw [h, e9, d0 _ (hz (3 * j) (by omega))]
    rfl
  · have h := (dfK_sound (df_all hj (k := 3) (by norm_num))).2.2.1 (by norm_num) (by norm_num)
      (by norm_num) i hi
    have e3 : 27 * j + 3 - 3 = 27 * j + 0 := by omega
    rw [h, e3, d0 _ (hz (3 * j + 1) (by omega))]
  · have h := (dfK_sound (df_all hj (k := 1) (by norm_num))).2.1 (by norm_num) i hi
    have e1 : 27 * j + 1 - 1 = 27 * j + 0 := by omega
    rw [h, e1, d0 _ (hz (3 * j + 2) (by omega))]

@[expose] noncomputable def cgP (j m : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (unpack 3510 12 (CG (t12 gofC j + m)))

@[expose] noncomputable def cSub (j : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {g | ∃ m < t12 ngC j, cgP j m = g}


theorem rep_memP {k : ℕ} (hk : k < 15) : permOfArr 3510 (repXYZ[k]!) ∈ fi22P := by
  rw [(repXYZ_facts.2 _ hk).1]
  exact sf_mem (u := 34 + k) (by omega) (sfG_row hk) (repXYZ_facts.2 _ hk).2

theorem cgP_comm_gen {j m : ℕ} (hj : j < 5) (hm : m < t12 ngC j) {t e : ℕ}
    (hte : (t = 0 ∧ e = 9) ∨ (t = 1 ∧ e = 3) ∨ (t = 2 ∧ e = 1)) :
    cgP j m * permOfArr 3510 (repXYZ[3 * j + t]!) =
      permOfArr 3510 (repXYZ[3 * j + t]!) * cgP j m := by
  have hr := cgIdx_lt hj hm
  have hcR := prep_of_PP (cg_PP hr)
  have hk : 3 * j + t < 15 := by omega
  have hwR := rep_prep hk
  have he : e = 9 ∨ e = 3 ∨ e = 1 := by omega
  have hD := df_row hj hte
  refine Fi22Base.eq_on_base (mul_mem (cg_memP hr) (rep_memP hk))
    (mul_mem (rep_memP hk) (cg_memP hr)) fun b hb hmem => ?_
  have hl : ∃ l < 6, bp l = b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩, ⟨5, by norm_num, rfl⟩]
  obtain ⟨l, hl, rfl⟩ := hl
  have k := commK_pt (jx_commK hj hm) e he l hl
  have hcb : ap (CG (t12 gofC j + m)) (bp l) < 3510 := by
    rw [ap_eq hcR hb]
    exact pt_lt _ _ hb
  rw [hD _ hb, hD _ hcb, ap_eq hwR hb, ap_eq hcR hb,
    ap_eq hcR (pt_lt (MonoidHom.id _) (permOfArr 3510 (repXYZ[3 * j + t]!)) hb),
    ap_eq hwR (pt_lt (MonoidHom.id _) (permOfArr 3510 (unpack 3510 12 (CG (t12 gofC j + m)))) hb),
    ← pt_mul, ← pt_mul] at k
  unfold pt at k
  rw [dif_pos hb, dif_pos hb] at k
  exact k

theorem cSub_le_P {j : ℕ} (hj : j < 5) : cSub j ≤ fi22P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨m, hm, rfl⟩
  exact cg_memP (cgIdx_lt hj hm)

theorem cSub_le_cent {j : ℕ} (hj : j < 5) :
    cSub j ≤ Subgroup.centralizer (dSub j : Set (Equiv.Perm (Fin 3510))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨m, hm, rfl⟩
  have hD : dSub j ≤ Subgroup.centralizer {cgP j m} := by
    unfold dSub
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro _ rfl
    · exact cgP_comm_gen (t := 0) hj hm (Or.inl ⟨rfl, rfl⟩)
    · exact cgP_comm_gen (t := 1) hj hm (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact cgP_comm_gen (t := 2) hj hm (Or.inr (Or.inr ⟨rfl, rfl⟩))
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.1 (hD hx)) _ rfl).symm

end CertificateChecks.KernelFi22Twist

end
