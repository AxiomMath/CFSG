module

public import CFSG.Certificates.Kernel.FixBoundK.RepGlue
public import Certificates.Kernel.FixBoundK.PairFacts
public import Certificates.Kernel.FixBoundK.TrivGlue
public import Certificates.Kernel.FixBoundK.Mem0
public import Certificates.Kernel.FixBoundK.Mem1
public import Certificates.Kernel.FixBoundK.Mem2
public import Certificates.Kernel.FixBoundK.Mem3
public import Certificates.Kernel.FixBoundK.Mem4
public import Certificates.Kernel.FixBoundK.Mem5
public import Certificates.Kernel.FixBoundK.Mem6
public import Certificates.Kernel.FixBoundK.Mem7
public import Certificates.Kernel.FixBoundK.Mem8
public import Certificates.Kernel.FixBoundK.Mem9
public import Certificates.Kernel.FixBoundK.Fix0
public import Certificates.Kernel.FixBoundK.Fix1
public import Certificates.Kernel.FixBoundK.Fix2
public import Certificates.Kernel.FixBoundK.Fix3
public import Certificates.Kernel.FixBoundK.Fix4
public import Certificates.Kernel.FixBoundK.Fix5
public import Certificates.Kernel.FixBoundK.Fix6
public import Certificates.Kernel.FixBoundK.Fix7
public import Certificates.Kernel.FixBoundK.Fix8
public import Certificates.Kernel.FixBoundK.Fix9
public import CFSG.Certificates.Kernel.FixBoundK.TrivBound
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Monster.B.Short.ShortStab
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFixBoundK.RepFacts

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisQuot CFSG.KC.FixBoundK CFSG.KC.FixBoundK.Pair
  CertificateChecks.KernelFixBoundK.PairG CertificateChecks.KernelFixBoundK.FixData
  CertificateChecks.KernelFixBoundK.PairFacts

#kc_forall_tree c812201_fix0 (fun i => fixAt Mem0.reps Mem0.gens (nthS [] fx 0) i = true) 11
  CertificateChecks.KernelFixBoundK.Fix0.fix
#kc_forall_tree c812201_fix1 (fun i => fixAt Mem1.reps Mem1.gens (nthS [] fx 1) i = true) 31
  CertificateChecks.KernelFixBoundK.Fix1.fix
#kc_forall_tree c812201_fix2 (fun i => fixAt Mem2.reps Mem2.gens (nthS [] fx 2) i = true) 56
  CertificateChecks.KernelFixBoundK.Fix2.fix
#kc_forall_tree c812201_fix3 (fun i => fixAt Mem3.reps Mem3.gens (nthS [] fx 3) i = true) 65
  CertificateChecks.KernelFixBoundK.Fix3.fix
#kc_forall_tree c812201_fix4 (fun i => fixAt Mem4.reps Mem4.gens (nthS [] fx 4) i = true) 133
  CertificateChecks.KernelFixBoundK.Fix4.fix
#kc_forall_tree c812201_fix5 (fun i => fixAt Mem5.reps Mem5.gens (nthS [] fx 5) i = true) 95
  CertificateChecks.KernelFixBoundK.Fix5.fix
#kc_forall_tree c812201_fix6 (fun i => fixAt Mem6.reps Mem6.gens (nthS [] fx 6) i = true) 72
  CertificateChecks.KernelFixBoundK.Fix6.fix
#kc_forall_tree c812201_fix7 (fun i => fixAt Mem7.reps Mem7.gens (nthS [] fx 7) i = true) 159
  CertificateChecks.KernelFixBoundK.Fix7.fix
#kc_forall_tree c812201_fix8 (fun i => fixAt Mem8.reps Mem8.gens (nthS [] fx 8) i = true) 94
  CertificateChecks.KernelFixBoundK.Fix8.fix
#kc_forall_tree c812201_fix9 (fun i => fixAt Mem9.reps Mem9.gens (nthS [] fx 9) i = true) 35
  CertificateChecks.KernelFixBoundK.Fix9.fix

#kc_forall_tree c812201_fam0 (fun i => famAt Mem0.reps Mem0.ch FamData0.fc i = true) 11
  CertificateChecks.KernelFixBoundK.Fix0.fam
#kc_forall_tree c812201_fam1 (fun i => famAt Mem1.reps Mem1.ch FamData1.fc i = true) 31
  CertificateChecks.KernelFixBoundK.Fix1.fam
#kc_forall_tree c812201_fam2 (fun i => famAt Mem2.reps Mem2.ch FamData2.fc i = true) 56
  CertificateChecks.KernelFixBoundK.Fix2.fam
#kc_forall_tree c812201_fam3 (fun i => famAt Mem3.reps Mem3.ch FamData3.fc i = true) 65
  CertificateChecks.KernelFixBoundK.Fix3.fam
#kc_forall_tree c812201_fam4 (fun i => famAt Mem4.reps Mem4.ch FamData4.fc i = true) 133
  CertificateChecks.KernelFixBoundK.Fix4.fam
#kc_forall_tree c812201_fam5 (fun i => famAt Mem5.reps Mem5.ch FamData5.fc i = true) 95
  CertificateChecks.KernelFixBoundK.Fix5.fam
#kc_forall_tree c812201_fam6 (fun i => famAt Mem6.reps Mem6.ch FamData6.fc i = true) 72
  CertificateChecks.KernelFixBoundK.Fix6.fam
#kc_forall_tree c812201_fam7 (fun i => famAt Mem7.reps Mem7.ch FamData7.fc i = true) 159
  CertificateChecks.KernelFixBoundK.Fix7.fam
#kc_forall_tree c812201_fam8 (fun i => famAt Mem8.reps Mem8.ch FamData8.fc i = true) 94
  CertificateChecks.KernelFixBoundK.Fix8.fam
#kc_forall_tree c812201_fam9 (fun i => famAt Mem9.reps Mem9.ch FamData9.fc i = true) 35
  CertificateChecks.KernelFixBoundK.Fix9.fam

#kc_forall_tree c812201_ch0 (fun k => chAt Mem0.reps Mem0.ch k = true) 259
  CertificateChecks.KernelFixBoundK.Mem0.ch
#kc_forall_tree c812201_ch1 (fun k => chAt Mem1.reps Mem1.ch k = true) 269
  CertificateChecks.KernelFixBoundK.Mem1.ch
#kc_forall_tree c812201_ch2 (fun k => chAt Mem2.reps Mem2.ch k = true) 276
  CertificateChecks.KernelFixBoundK.Mem2.ch
#kc_forall_tree c812201_ch3 (fun k => chAt Mem3.reps Mem3.ch k = true) 280
  CertificateChecks.KernelFixBoundK.Mem3.ch
#kc_forall_tree c812201_ch4 (fun k => chAt Mem4.reps Mem4.ch k = true) 350
  CertificateChecks.KernelFixBoundK.Mem4.ch
#kc_forall_tree c812201_ch5 (fun k => chAt Mem5.reps Mem5.ch k = true) 319
  CertificateChecks.KernelFixBoundK.Mem5.ch
#kc_forall_tree c812201_ch6 (fun k => chAt Mem6.reps Mem6.ch k = true) 308
  CertificateChecks.KernelFixBoundK.Mem6.ch
#kc_forall_tree c812201_ch7 (fun k => chAt Mem7.reps Mem7.ch k = true) 387
  CertificateChecks.KernelFixBoundK.Mem7.ch
#kc_forall_tree c812201_ch8 (fun k => chAt Mem8.reps Mem8.ch k = true) 330
  CertificateChecks.KernelFixBoundK.Mem8.ch
#kc_forall_tree c812201_ch9 (fun k => chAt Mem9.reps Mem9.ch k = true) 119
  CertificateChecks.KernelFixBoundK.Mem9.ch

theorem len0 : Mem0.ch.length = 259 := by decide +kernel
theorem len1 : Mem1.ch.length = 269 := by decide +kernel
theorem len2 : Mem2.ch.length = 276 := by decide +kernel
theorem len3 : Mem3.ch.length = 280 := by decide +kernel
theorem len4 : Mem4.ch.length = 350 := by decide +kernel
theorem len5 : Mem5.ch.length = 319 := by decide +kernel
theorem len6 : Mem6.ch.length = 308 := by decide +kernel
theorem len7 : Mem7.ch.length = 387 := by decide +kernel
theorem len8 : Mem8.ch.length = 330 := by decide +kernel
theorem len9 : Mem9.ch.length = 119 := by decide +kernel

@[expose] def SrcOK (t : ℕ) : Prop :=
  ∃ gens : List (List ℕ),
    Subgroup.closure (srcSet IV RG t) = (Subgroup.closure (GenSet gens)).map AutPerm.subtype ∧
    (CFSG.Open.IsElemAbelian 2 (Subgroup.closure (GenSet gens)) →
      FixBoundAt (Subgroup.closure (GenSet gens)))

theorem src_of_file (hb : BasicsSem) {lo n nch : ℕ} {reps : List Rep}
    {gens : List (List (List ℕ))} {ch : List (ℕ × List Mem)} {fx : List FixD}
    {fc : List (List FamC)}
    (hR : ∀ i < n, repAtP IV RG B nB 191 lo reps gens i = true)
    (hF : ∀ i < n, fixAt reps gens fx i = true) (hA : ∀ i < n, famAt reps ch fc i = true)
    (hC : ∀ k < nch, chAt reps ch k = true) (hl : ch.length = nch)
    {t : ℕ} (ht : t ≤ 751) (ht0 : t ≠ 0) (h1 : lo ≤ t - 1) (h2 : t - 1 < lo + n) : SrcOK t := by
  have hi : t - 1 - lo < n := by omega
  have hrep := hR _ hi
  have e : Nat.add lo (t - 1 - lo) = t - 1 := by
    rw [Nat.add_eq]
    omega
  rw [repAtP, e] at hrep
  simp only [CFSG.KC.FixBoundK.TrivSound.nthS_eq] at hrep
  obtain ⟨hgen, hcl⟩ := src_genSet checkFacts ht ht0 hrep
  exact ⟨_, hcl, fun hP => fixBoundAt_rep hb (hF _ hi) (hA _ hi) hC hl.le hgen hP⟩

theorem rep_src (hb : BasicsSem) : ∀ t ≤ 751, t ≠ 0 → SrcOK t := by
  intro t ht ht0
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
  rcases Nat.lt_or_ge (t - 1) 11 with h | h0
  · exact src_of_file hb c812201_m0 c812201_fix0 c812201_fam0 c812201_ch0 len0 ht ht0
      (by rw [l0]; omega) (by rw [l0]; omega)
  rcases Nat.lt_or_ge (t - 1) 42 with h | h1
  · exact src_of_file hb c812201_m1 c812201_fix1 c812201_fam1 c812201_ch1 len1 ht ht0
      (by rw [l1]; omega) (by rw [l1]; omega)
  rcases Nat.lt_or_ge (t - 1) 98 with h | h2
  · exact src_of_file hb c812201_m2 c812201_fix2 c812201_fam2 c812201_ch2 len2 ht ht0
      (by rw [l2]; omega) (by rw [l2]; omega)
  rcases Nat.lt_or_ge (t - 1) 163 with h | h3
  · exact src_of_file hb c812201_m3 c812201_fix3 c812201_fam3 c812201_ch3 len3 ht ht0
      (by rw [l3]; omega) (by rw [l3]; omega)
  rcases Nat.lt_or_ge (t - 1) 296 with h | h4
  · exact src_of_file hb c812201_m4 c812201_fix4 c812201_fam4 c812201_ch4 len4 ht ht0
      (by rw [l4]; omega) (by rw [l4]; omega)
  rcases Nat.lt_or_ge (t - 1) 391 with h | h5
  · exact src_of_file hb c812201_m5 c812201_fix5 c812201_fam5 c812201_ch5 len5 ht ht0
      (by rw [l5]; omega) (by rw [l5]; omega)
  rcases Nat.lt_or_ge (t - 1) 463 with h | h6
  · exact src_of_file hb c812201_m6 c812201_fix6 c812201_fam6 c812201_ch6 len6 ht ht0
      (by rw [l6]; omega) (by rw [l6]; omega)
  rcases Nat.lt_or_ge (t - 1) 622 with h | h7
  · exact src_of_file hb c812201_m7 c812201_fix7 c812201_fam7 c812201_ch7 len7 ht ht0
      (by rw [l7]; omega) (by rw [l7]; omega)
  rcases Nat.lt_or_ge (t - 1) 716 with h | h8
  · exact src_of_file hb c812201_m8 c812201_fix8 c812201_fam8 c812201_ch8 len8 ht ht0
      (by rw [l8]; omega) (by rw [l8]; omega)
  · exact src_of_file hb c812201_m9 c812201_fix9 c812201_fam9 c812201_ch9 len9 ht ht0
      (by rw [l9]; omega) (by rw [l9]; change t - 1 < 716 + 35; omega)

theorem srcSet_zero : srcSet IV RG 0 = ∅ := by
  rw [srcSet, srcR_zero, rk_zero]
  simp

theorem trivCond : TrivCond := fun _ hx => TrivGlue.triv_case hx

theorem fixBound (hb : BasicsSem) : FixBound :=
  fixBound_of_src (src := srcSet IV RG) exists_conj_eq_src srcSet_zero (rep_src hb)
    (fixBoundAt_bot trivCond)

end CertificateChecks.KernelFixBoundK.RepFacts

end
