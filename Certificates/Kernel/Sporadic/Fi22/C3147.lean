
module

public import Certificates.Kernel.Sporadic.Fi22.C3147Base

public import Certificates.Kernel.Sporadic.Fi22.R3147B7
public import Certificates.Kernel.Sporadic.Fi22.R3147B6
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.S3147
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import CFSG.Certificates.NativeValidSchreier
public import CFSG.Certificates.SchreierChainOrderStabilizers
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem strong_le : Subgroup.closure {g : Equiv.Perm (Fin 3510) |
    ∃ j < fi22StrongArrs.size, permOfArr 3510 fi22StrongArrs[j]! = g} ≤ fi22P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < 19 := by simpa [fi22StrongArrs] using hj
  have h := fi22Chain_strong_mem ⟨j, hj'⟩
  rw [fi22Chain_strong_get] at h
  rw [fi22StrongArrs_get hj']
  exact h

theorem sep7 :
    Sep 3510 fi22StrongArrs B7 := by
  intro G hG hfix
  refine Fi22S.fi22P_formSep (strong_le hG) fun r hr h => ?_
  simp only [fi22CentralizerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fix_of_base hfix 0 (by decide) 0 rfl h
  · exact fix_of_base hfix 1 (by decide) 1 rfl h
  · exact fix_of_base hfix 2 (by decide) 2 rfl h
  · exact fix_of_base hfix 3 (by decide) 3 rfl h
  · exact fix_of_base hfix 5 (by decide) 4 rfl h
  · exact fix_of_base hfix 6 (by decide) 10 rfl h

theorem chain7Arrays :
    ChainArrays fi22Chain7 fi22OrigArrs fi22StrongArrs B7 fi22WordArrs where
  orig_size := by simp [fi22OrigArrs]; rfl
  strong_size := by simp [fi22StrongArrs]; rfl
  base_size := rfl
  orig k := by
    have hk : (k : ℕ) < 2 := k.2
    rw [getElem!_pos _ (k : ℕ) (by simp [fi22OrigArrs, hk]), chain7_original_get]
    simp only [fi22OrigArrs, Array.getElem_ofFn]
    exact rep_fi22Gen hk
  strong j := by
    have hj : (j : ℕ) < 19 := j.2
    rw [chain7_strong_get]
    exact rep_fi22Strong hj
  base_val i := by
    have hi : (i : ℕ) < 7 := i.2
    change (((#v[0, 1, 2, 3, 6, 4, 10] : Vector (Fin 3510) 7).get ⟨i, hi⟩ : Fin 3510) : ℕ) =
      B7[(i : ℕ)]!
    obtain ⟨i, hi⟩ := i
    revert i
    decide
  deriv j hj := by
    have hj' : (j : ℕ) < 19 := j.2
    rw [getElem!_pos _ (j : ℕ) (by simp [fi22WordArrs, hj'])]
    simp only [fi22WordArrs, Array.getElem_ofFn]
    rfl

theorem chain7_ok :
    rawChainOK 3510 fi22OrigArrs fi22StrongArrs B7 fi22WordArrs 4 = true :=
  rawChainOK_arrays (rawChainTK_sound binds7 Fi22R7.head Fi22R7.tl Fi22R7.hst sep7 Fi22R7.hs
    (by norm_num))

theorem fix10
    {G : Equiv.Perm (Fin 3510)} (hG : G ∈ fi22P)
    (hfix : ∀ b ∈ fi22Chain7.base.toList.take 6, G b = b) : G 10 = 10 := by
  have hv := validSchreier_of_chainOK chain7Arrays (by norm_num) chain7_ok
  have hmem : G ∈ fi22Chain7.levelSubgroup 6 :=
    (fi22Chain7.mem_levelSubgroup_iff hv.1 6 (by decide) G).2 ⟨hG, hfix⟩
  let i6 : Fin fi22Chain7.baseCount := ⟨6, by decide⟩
  have hcard : Nat.card (fi22Chain7.orbitPoints i6) = 1 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, hv.2 i6]
    change ((rawLevels 3510 fi22StrongArrs B7)[6]!).pts.size = 1
    rw [rawLevels_get (by decide),
      (levelTK_sound binds7 Fi22R7.head Fi22R7.tl (i := 6) (by norm_num)).2]
    exact Nat.eq_of_beq_eq_true last7
  have hsub : Subsingleton (fi22Chain7.orbitPoints i6) :=
    (Nat.card_eq_one_iff_unique.1 hcard).1
  rw [RawSchreierDatum.orbitPoints_eq_orbit] at hsub
  have h1 : (⟨G, hmem⟩ : fi22Chain7.levelSubgroup 6) • fi22Chain7.base.get i6 ∈
      MulAction.orbit (fi22Chain7.levelSubgroup i6.val) (fi22Chain7.base.get i6) :=
    MulAction.mem_orbit _ _
  have h2 : fi22Chain7.base.get i6 ∈
      MulAction.orbit (fi22Chain7.levelSubgroup i6.val) (fi22Chain7.base.get i6) :=
    MulAction.mem_orbit_self _
  have e := congrArg Subtype.val (Subsingleton.elim (α := MulAction.orbit
    (fi22Chain7.levelSubgroup i6.val) (fi22Chain7.base.get i6)) ⟨_, h1⟩ ⟨_, h2⟩)
  exact e

theorem sep6 :
    Sep 3510 fi22StrongArrs fi22BaseArr := by
  intro G hG hfix
  have hP := strong_le hG
  have h10 : G 10 = 10 := by
    refine fix10 hP fun b hb => ?_
    have e : fi22Chain7.base.toList.take 6 = [0, 1, 2, 3, 6, 4] := by decide
    rw [e] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fix_of_base hfix 0 (by decide) 0 rfl (by norm_num)
    · exact fix_of_base hfix 1 (by decide) 1 rfl (by norm_num)
    · exact fix_of_base hfix 2 (by decide) 2 rfl (by norm_num)
    · exact fix_of_base hfix 3 (by decide) 3 rfl (by norm_num)
    · exact fix_of_base hfix 4 (by decide) 6 rfl (by norm_num)
    · exact fix_of_base hfix 5 (by decide) 4 rfl (by norm_num)
  refine Fi22S.fi22P_formSep hP fun r hr h => ?_
  simp only [fi22CentralizerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fix_of_base hfix 0 (by decide) 0 rfl h
  · exact fix_of_base hfix 1 (by decide) 1 rfl h
  · exact fix_of_base hfix 2 (by decide) 2 rfl h
  · exact fix_of_base hfix 3 (by decide) 3 rfl h
  · exact fix_of_base hfix 5 (by decide) 4 rfl h
  · exact h10

theorem facts3147 :
    (rawChainOK 3510 fi22OrigArrs fi22StrongArrs fi22BaseArr fi22WordArrs 4 = true ∧
       rawOrbitSizes 3510 fi22StrongArrs fi22BaseArr = [3510, 2816, 567, 720, 8, 2])
    ∧ (eqA 3510 (powA 3510 (fi22ChainGen 0) 2) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 0) (idA 3510) = false ∧
       eqA 3510 (powA 3510 (fi22ChainGen 1) 13) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 1) (idA 3510) = false ∧
       eqA 3510 (powA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) 11) (idA 3510) = true ∧
       eqA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (idA 3510) = false) :=
  ⟨⟨rawChainOK_arrays (rawChainTK_sound binds6 Fi22R6.head Fi22R6.tl Fi22R6.hst sep6 Fi22R6.hs
      (by norm_num)),
    by rw [rawOrbitSizesTK_sound binds6 Fi22R6.head Fi22R6.tl, orbits6]⟩, Fi22G.orders⟩

open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
theorem certificate3147_of :
 (rawChainOK 3510 fi22OrigArrs fi22StrongArrs fi22BaseArr fi22WordArrs 4 = true ∧
       rawOrbitSizes 3510 fi22StrongArrs fi22BaseArr = [3510, 2816, 567, 720, 8, 2])
    ∧ (eqA 3510 (powA 3510 (fi22ChainGen 0) 2) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 0) (idA 3510) = false ∧
       eqA 3510 (powA 3510 (fi22ChainGen 1) 13) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 1) (idA 3510) = false ∧
       eqA 3510 (powA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) 11) (idA 3510) = true ∧
       eqA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (idA 3510) = false) :=
  facts3147

end CertificateChecks.KernelSpor.Fi22C3147

end
