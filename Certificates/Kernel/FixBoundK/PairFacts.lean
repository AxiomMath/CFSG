module

public import CFSG.Certificates.Kernel.FixBoundK.Step
public import CFSG.Certificates.Kernel.FixBoundK.TrivSound
public import CFSG.Certificates.Kernel.Common.ForallTreeFrom
public import Certificates.Certificate3018
public import Certificates.Kernel.FixBoundK.PairBase
public import Certificates.Kernel.FixBoundK.PairRep
public import Certificates.Kernel.FixBoundK.Pair0
public import Certificates.Kernel.FixBoundK.Pair1
public import Certificates.Kernel.FixBoundK.Pair2
public import Certificates.Kernel.FixBoundK.Pair3
public import Certificates.Kernel.FixBoundK.PairCp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFixBoundK.PairFacts

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.FixBoundK
  CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG CertificateChecks.Perm3018
  Subgroup

@[expose] noncomputable def items (s : ℕ) : List Item :=
  (nthS (nat_lit 0, []) PairD.src s).2

#kc_forall_tree c812201_inv (fun i => invOK IV IR recS 191 i = true) 191
  CertificateChecks.KernelFixBoundK.PairBase.inv

#kc_forall_tree c812201_base
  (fun c => allN 64 (fun l => baseOK B nB recS (64 * c + l)) = true) 16
  CertificateChecks.KernelFixBoundK.PairBase.base

#kc_forall_tree c812201_cm (fun a => cmOK IV CM B nB 191 a = true) 191
  CertificateChecks.KernelFixBoundK.PairBase.cm

#kc_forall_tree c812201_m0 (fun i => repAtP IV RG B nB 191 Mem0.lo Mem0.reps Mem0.gens i = true)
  11 CertificateChecks.KernelFixBoundK.PairRep.m0r
#kc_forall_tree c812201_m1 (fun i => repAtP IV RG B nB 191 Mem1.lo Mem1.reps Mem1.gens i = true)
  31 CertificateChecks.KernelFixBoundK.PairRep.m1r
#kc_forall_tree c812201_m2 (fun i => repAtP IV RG B nB 191 Mem2.lo Mem2.reps Mem2.gens i = true)
  56 CertificateChecks.KernelFixBoundK.PairRep.m2r
#kc_forall_tree c812201_m3 (fun i => repAtP IV RG B nB 191 Mem3.lo Mem3.reps Mem3.gens i = true)
  65 CertificateChecks.KernelFixBoundK.PairRep.m3r
#kc_forall_tree c812201_m4 (fun i => repAtP IV RG B nB 191 Mem4.lo Mem4.reps Mem4.gens i = true)
  133 CertificateChecks.KernelFixBoundK.PairRep.m4r
#kc_forall_tree c812201_m5 (fun i => repAtP IV RG B nB 191 Mem5.lo Mem5.reps Mem5.gens i = true)
  95 CertificateChecks.KernelFixBoundK.PairRep.m5r
#kc_forall_tree c812201_m6 (fun i => repAtP IV RG B nB 191 Mem6.lo Mem6.reps Mem6.gens i = true)
  72 CertificateChecks.KernelFixBoundK.PairRep.m6r
#kc_forall_tree c812201_m7 (fun i => repAtP IV RG B nB 191 Mem7.lo Mem7.reps Mem7.gens i = true)
  159 CertificateChecks.KernelFixBoundK.PairRep.m7r
#kc_forall_tree c812201_m8 (fun i => repAtP IV RG B nB 191 Mem8.lo Mem8.reps Mem8.gens i = true)
  94 CertificateChecks.KernelFixBoundK.PairRep.m8r
#kc_forall_tree c812201_m9 (fun i => repAtP IV RG B nB 191 Mem9.lo Mem9.reps Mem9.gens i = true)
  35 CertificateChecks.KernelFixBoundK.PairRep.m9r

#kc_forall_tree c812201_src0
  (fun i => srcAt IV RG CM B nB 1024 751 191 recS PairD.lo PairD.src i = true) 188
  CertificateChecks.KernelFixBoundK.Pair0.src
#kc_forall_tree_from c812201_src1
  (fun i => srcAt IV RG CM B nB 1024 751 191 recS PairD.lo PairD.src i = true) 188 188
  CertificateChecks.KernelFixBoundK.Pair1.src
#kc_forall_tree_from c812201_src2
  (fun i => srcAt IV RG CM B nB 1024 751 191 recS PairD.lo PairD.src i = true) 376 188
  CertificateChecks.KernelFixBoundK.Pair2.src
#kc_forall_tree_from c812201_src3
  (fun i => srcAt IV RG CM B nB 1024 751 191 recS PairD.lo PairD.src i = true) 564 188
  CertificateChecks.KernelFixBoundK.Pair3.src

theorem bp_lt : ∀ k < nB, bp B k < 24 := by decide +kernel

theorem base_all : ∀ j < 1024, baseOK B nB recS j = true := by
  intro j hj
  have h := (allN_iff _ _).1 (c812201_base (j / 64) (by change j / 64 < 16; omega)) (j % 64)
    (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem rep_of {lo n : ℕ} {reps : List Rep} {gens : List (List (List ℕ))}
    (h : ∀ i < n, repAtP IV RG B nB 191 lo reps gens i = true) {t : ℕ} (h1 : lo ≤ t)
    (h2 : t < lo + n) : ∃ r gl, repOK IV RG B nB 191 t r gl = true := by
  have e : Nat.add lo (t - lo) = t := by
    rw [Nat.add_eq]
    omega
  refine ⟨(nthS repD reps (t - lo)).1, nthS [] gens (t - lo), ?_⟩
  have := h (t - lo) (by omega)
  rwa [repAtP, e] at this

theorem rep_all : ∀ t < 751, ∃ r gl, repOK IV RG B nB 191 t r gl = true := by
  intro t ht
  have l0 : Mem0.lo = 0 := rfl
  have l1 : Mem1.lo = 11 := rfl
  have l2 : Mem2.lo = 42 := rfl
  have l3 : Mem3.lo = 98 := rfl
  have l4 : Mem4.lo = 163 := rfl
  have l5 : Mem5.lo = 296 := rfl
  have l6 : Mem6.lo = 391 := rfl
  have l7 : Mem7.lo = 463 := rfl
  have l8 : Mem8.lo = 622 := rfl
  have l9 : Mem9.lo = 716 := rfl
  rcases Nat.lt_or_ge t 11 with h | h0
  · exact rep_of c812201_m0 (by rw [l0]; omega) (by rw [l0]; omega)
  rcases Nat.lt_or_ge t 42 with h | h1
  · exact rep_of c812201_m1 (by rw [l1]; omega) (by rw [l1]; omega)
  rcases Nat.lt_or_ge t 98 with h | h2
  · exact rep_of c812201_m2 (by rw [l2]; omega) (by rw [l2]; omega)
  rcases Nat.lt_or_ge t 163 with h | h3
  · exact rep_of c812201_m3 (by rw [l3]; omega) (by rw [l3]; omega)
  rcases Nat.lt_or_ge t 296 with h | h4
  · exact rep_of c812201_m4 (by rw [l4]; omega) (by rw [l4]; omega)
  rcases Nat.lt_or_ge t 391 with h | h5
  · exact rep_of c812201_m5 (by rw [l5]; omega) (by rw [l5]; omega)
  rcases Nat.lt_or_ge t 463 with h | h6
  · exact rep_of c812201_m6 (by rw [l6]; omega) (by rw [l6]; omega)
  rcases Nat.lt_or_ge t 622 with h | h7
  · exact rep_of c812201_m7 (by rw [l7]; omega) (by rw [l7]; omega)
  rcases Nat.lt_or_ge t 716 with h | h8
  · exact rep_of c812201_m8 (by rw [l8]; omega) (by rw [l8]; omega)
  · exact rep_of c812201_m9 (by rw [l9]; omega) (by rw [l9]; omega)

theorem srcAt_all : ∀ s < 752,
    srcAt IV RG CM B nB 1024 751 191 recS PairD.lo PairD.src s = true := by
  intro s hs
  rcases Nat.lt_or_ge s 188 with h | h0
  · exact c812201_src0 s h
  rcases Nat.lt_or_ge s 376 with h | h1
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h0
    exact c812201_src1 k (by change k < 188; omega)
  rcases Nat.lt_or_ge s 564 with h | h2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact c812201_src2 k (by change k < 188; omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
    exact c812201_src3 k (by change k < 188; omega)

theorem src_all : ∀ s ≤ 751, srcOK IV RG CM B nB 1024 751 191 recS s (items s) = true := by
  intro s hs
  have h := srcAt_all s (by omega)
  have hlo : PairD.lo = 0 := rfl
  rw [srcAt] at h
  simp only [TrivSound.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  rw [hlo, Nat.add_eq, Nat.zero_add] at h
  have h2 := h.2
  rw [h.1] at h2
  exact h2

theorem cp_all : ∀ s ≤ 751, ∀ it ∈ items s, cpItem nB it = true := by
  intro s _ it hit
  have h := PairCp.cpOK
  rw [cpAll, TrivSound.allS_iff] at h
  rw [items, TrivSound.nthS_eq] at hit
  rcases Nat.lt_or_ge s PairD.src.length with hl | hl
  · rw [List.getD_eq_getElem _ _ hl] at hit
    exact (TrivSound.allS_iff _ _).1 (h _ (List.getElem_mem hl)) it hit
  · rw [List.getD_eq_default _ _ hl] at hit
    exact absurd hit List.not_mem_nil

theorem checkFacts : CheckFacts recS IV IR RG CM B nB items := by
  obtain ⟨hm, -, hrec, hlt⟩ := Batch3018.sylowF.2.2
  exact ⟨hm, hrec, hlt, bp_lt, base_all, c812201_inv, c812201_cm, rep_all, src_all, cp_all⟩

theorem exists_conj_eq_src (P : Subgroup (Equiv.Perm (Fin 24))) (hPE : P ≤ sylowSub)
    (hP : CFSG.Open.IsElemAbelian 2 P) :
    ∃ t ≤ 751, ∃ g ∈ sylowSub, conjG g P = closure (srcSet IV RG t) :=
  CFSG.KC.FixBoundK.Pair.exists_conj_eq_srcSet checkFacts P hPE hP

end CertificateChecks.KernelFixBoundK.PairFacts

end
