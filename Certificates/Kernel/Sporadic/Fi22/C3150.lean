
module

public import Certificates.Kernel.Sporadic.Fi22.S3150
public import Certificates.Kernel.Sporadic.Fi22.C3147
public import CFSG.Monster.B.Fischer.Fi22Order

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3150

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor

theorem outM_eq {j : Nat} (hj : j < 17) :
    (fi22OuterStrong3510 3)[j]! = unpack 3510 12 (Fi22M3.MS j) := by
  have hl : fi22OuterLine3510 3 j = 3 + j := by
    unfold fi22OuterLine3510
    simp [fi22OuterLines3510]
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ j (by simpa [fi22OuterLines3510] using hj), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 3 j) = _
  rw [hl]
  exact Fi22X.line_of Fi22OutT.eq (Fi22X.asciiK_take Fi22X.outAscii (by simp only [Nat.mul_eq]; omega))
    (Fi22M3.all j hj)

theorem bindsM : Binds 3510 12 Fi22MR.S 17 6 Fi22MR.BP (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22OuterStrong3510, fi22OuterLines3510],
    fun j hj => ?_, by simp, fun t ht => Nat.eq_of_beq_eq_true (allN_spec Fi22S3150.baseM t ht)⟩
  rw [outM_eq hj, Nat.eq_of_beq_eq_true (allN_spec Fi22S3150.sM j hj)]

theorem bindsT : Binds 3510 12 Fi22TR.S 13 6 Fi22TR.BP (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22OuterStrong3510, fi22OuterLines3510],
    fun j hj => ?_, by simp, fun t ht => Nat.eq_of_beq_eq_true (allN_spec Fi22S3150.baseT t ht)⟩
  rw [Fi22X.outT_eq hj, Nat.eq_of_beq_eq_true (allN_spec Fi22S3150.sT j hj)]

theorem sizeM : (fi22OuterStrong3510 3).size = 17 := by
  simp [fi22OuterStrong3510, fi22OuterLines3510]

theorem sizeT : (fi22OuterStrong3510 4).size = 13 := by
  simp [fi22OuterStrong3510, fi22OuterLines3510]

theorem hdM : Orb.Hd 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] 3
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 17 fi22OuterMDerivations) :=
  Orb.hd_of_head (by rw [sizeM]; omega) (rawHeadK_sound bindsM Fi22MR.head)

theorem hdT : Orb.Hd 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 9
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 13 fi22OuterTDerivations) :=
  Orb.hd_of_head (by rw [sizeT]; omega) (rawHeadK_sound bindsT Fi22TR.head)

theorem siftA_of {q : Nat} {g : Array Nat} (hg : g = unpack 3510 12 q)
    (hc : Fi22S3150.cn q = true) (hs : Fi22S3150.siftP q = true) :
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g = true :=
  siftK_sound Fi22X.bindsP Fi22X.permP Fi22PC.hl hg (range_of_canonK hc) hs

theorem siftM {k : Nat} (hk : k < 3) :
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
      (fi22OuterStrong3510 3)[k]! = true :=
  siftA_of (outM_eq (by omega)) (allN_spec Fi22S3150.cnM k hk) (allN_spec Fi22S3150.siftM k hk)

theorem siftT {k : Nat} (hk : k < 9) :
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
      (fi22OuterStrong3510 4)[k]! = true :=
  siftA_of (Fi22X.outT_eq (by omega)) (allN_spec Fi22S3150.cnT k hk) (allN_spec Fi22S3150.siftT k hk)

theorem fixM {k : Nat} (hk : k < 3) : ((fi22OuterStrong3510 3)[k]!)[0]! = 0 := by
  rw [outM_eq (by omega), Orb.unpack_get (n := 3510) (by norm_num)]
  exact Nat.eq_of_beq_eq_true (allN_spec Fi22S3150.fixM k hk)

theorem mem_of_siftA
    {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G)
    (h : siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g = true) :
    G ∈ fi22P :=
  (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hG).1 h

theorem sepP
    {G : Equiv.Perm (Fin 3510)} (hP : G ∈ fi22P)
    (hfix : ∀ r ∈ [0, 1, 2, 3, 4, 6], ∀ h : r < 3510, G ⟨r, h⟩ = ⟨r, h⟩) : G = 1 := by
  have h10 : G 10 = 10 := by
    refine Fi22C3147.fix10 hP fun b hb => ?_
    have e : Fi22C3147.fi22Chain7.base.toList.take 6 = [0, 1, 2, 3, 6, 4] := by decide
    rw [e] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfix 0 (by simp) (by norm_num)
    · exact hfix 1 (by simp) (by norm_num)
    · exact hfix 2 (by simp) (by norm_num)
    · exact hfix 3 (by simp) (by norm_num)
    · exact hfix 6 (by simp) (by norm_num)
    · exact hfix 4 (by simp) (by norm_num)
  refine Fi22S.fi22P_formSep hP fun r hr h => ?_
  simp only [fi22CentralizerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfix 0 (by simp) h
  · exact hfix 1 (by simp) h
  · exact hfix 2 (by simp) h
  · exact hfix 3 (by simp) h
  · exact hfix 4 (by simp) h
  · exact h10

theorem sepOf {S : Array (Array Nat)} {base : Array Nat} {kO : Nat} {W : Array (List Int)}
    (hd : Orb.Hd 3510 S base kO W) (hO : ∀ j < kO, permOfArr 3510 S[j]! ∈ fi22P)
    (hB : ∀ G ∈ fi22P, (∀ t < base.size, ∀ h : base[t]! < 3510,
      G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → G = 1) : Sep 3510 S base := by
  intro G hG hfix
  refine hB G ((Subgroup.closure_le _).2 ?_ hG) hfix
  rintro _ ⟨j, hj, rfl⟩
  have h := Orb.S_mem_Gen hd j hj
  unfold Orb.Gen at h
  refine (Subgroup.closure_le _).2 ?_ h
  rintro _ ⟨i, rfl⟩
  exact hO i i.2

theorem sepM :
    Sep 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] := by
  refine sepOf hdM (fun j hj => mem_of_siftA (Orb.rep_S hdM (by rw [sizeM]; omega)) (siftM hj))
    fun G hP hfix => sepP hP fun r hr h => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Fi22C3147.fix_of_base hfix 0 (by decide) 0 rfl h
  · exact Fi22C3147.fix_of_base hfix 1 (by decide) 1 rfl h
  · exact Fi22C3147.fix_of_base hfix 2 (by decide) 2 rfl h
  · exact Fi22C3147.fix_of_base hfix 5 (by decide) 3 rfl h
  · exact Fi22C3147.fix_of_base hfix 4 (by decide) 4 rfl h
  · exact Fi22C3147.fix_of_base hfix 3 (by decide) 6 rfl h

theorem sepT :
    Sep 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] := by
  refine sepOf hdT (fun j hj => mem_of_siftA (Orb.rep_S hdT (by rw [sizeT]; omega)) (siftT hj))
    fun G hP hfix => sepP hP fun r hr h => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Fi22C3147.fix_of_base hfix 0 (by decide) 0 rfl h
  · exact Fi22C3147.fix_of_base hfix 1 (by decide) 1 rfl h
  · exact Fi22C3147.fix_of_base hfix 2 (by decide) 2 rfl h
  · exact Fi22C3147.fix_of_base hfix 3 (by decide) 3 rfl h
  · exact Fi22C3147.fix_of_base hfix 5 (by decide) 4 rfl h
  · exact Fi22C3147.fix_of_base hfix 4 (by decide) 6 rfl h

theorem facts3150 :
    rawChainOK 3510 ((fi22OuterStrong3510 3).extract 0 fi22OuterMGenCount)
        (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3]
        (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] =
        [1, 2816, 567, 320, 18, 2] ∧
      rawChainOK 3510 ((fi22OuterStrong3510 4).extract 0 fi22OuterTGenCount)
        (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4]
        (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] = [1024, 32, 4, 1, 1, 1] ∧
      (∀ k < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 3)[k]! = true) ∧
      (∀ k < 3, ((fi22OuterStrong3510 3)[k]!)[0]! = 0) ∧
      (∀ k < 9, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 4)[k]! = true) :=
  ⟨rawChainTK_sound bindsM Fi22MR.head Fi22MR.tl Fi22MR.hst sepM Fi22MR.hs (by norm_num),
    by rw [rawOrbitSizesTK_sound bindsM Fi22MR.head Fi22MR.tl, Fi22S3150.orbM],
    rawChainTK_sound bindsT Fi22TR.head Fi22TR.tl Fi22TR.hst sepT Fi22TR.hs (by norm_num),
    by rw [rawOrbitSizesTK_sound bindsT Fi22TR.head Fi22TR.tl, Fi22S3150.orbT],
    fun _ hk => siftM hk, fun _ hk => fixM hk, fun _ hk => siftT hk⟩

open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
theorem certificate3150_of :
 rawChainOK 3510 ((fi22OuterStrong3510 3).extract 0 fi22OuterMGenCount)
        (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3]
        (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] =
        [1, 2816, 567, 320, 18, 2] ∧
      rawChainOK 3510 ((fi22OuterStrong3510 4).extract 0 fi22OuterTGenCount)
        (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4]
        (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] = [1024, 32, 4, 1, 1, 1] ∧
      (∀ k < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 3)[k]! = true) ∧
      (∀ k < 3, ((fi22OuterStrong3510 3)[k]!)[0]! = 0) ∧
      (∀ k < 9, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 4)[k]! = true) :=
  facts3150

end CertificateChecks.KernelSpor.Fi22C3150

end
