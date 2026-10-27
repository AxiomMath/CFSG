module

public import Certificates.Kernel.HS100.S5CData
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.HSStd
open CFSG.Monster.B.Co2 (allLt_iff)

theorem s5cTab_eq {k : ℕ} (hk : k < 4) : s5cTab k = unpack 100 7 (SC.F k) := by
  rw [s5cTab, SC.eq]
  exact hexTable3_sound SC.all k hk

theorem s5cS_eq {i : ℕ} (hi : i < 4) : s5cS[i]! = unpack 100 7 (SC.F i) := by
  interval_cases i <;> exact s5cTab_eq (by norm_num)

theorem ppSC {i : ℕ} (hi : i < 4) : PP 100 7 (SC.F i) :=
  PP_of_permOK hw (allN_spec S5.permS i hi)

theorem arr5_get0 {α} [Inhabited α] (a b c d e : α) : #[a, b, c, d, e][0]! = a := rfl
theorem arr5_get1 {α} [Inhabited α] (a b c d e : α) : #[a, b, c, d, e][1]! = b := rfl
theorem arr5_get2 {α} [Inhabited α] (a b c d e : α) : #[a, b, c, d, e][2]! = c := rfl
theorem arr5_get3 {α} [Inhabited α] (a b c d e : α) : #[a, b, c, d, e][3]! = d := rfl
theorem arr5_get4 {α} [Inhabited α] (a b c d e : α) : #[a, b, c, d, e][4]! = e := rfl
theorem arr5_size {α} (a b c d e : α) : #[a, b, c, d, e].size = 5 := rfl

theorem s5_gens : s5cGens.size = S5.ng ∧ ∀ k < S5.ng, s5cGens[k]! = unpack 100 7 (S5.G k) := by
  have h := S5.gensF
  rw [Bool.and_eq_true] at h
  refine ⟨by rw [s5cGens, arr5_size]; rfl, fun k hk => ?_⟩
  have hk5 : k < 5 := hk
  rcases k with _ | _ | _ | _ | _ | k
  · rw [Nat.eq_of_beq_eq_true h.1, s5cGens, arr5_get0]
    exact fiveLine_eq (j := 2) (by norm_num)
  · rw [Nat.eq_of_beq_eq_true (allN_spec h.2 0 (by norm_num)), s5cGens, arr5_get1]
    exact s5cTab_eq (by norm_num)
  · rw [Nat.eq_of_beq_eq_true (allN_spec h.2 1 (by norm_num)), s5cGens, arr5_get2]
    exact s5cTab_eq (by norm_num)
  · rw [Nat.eq_of_beq_eq_true (allN_spec h.2 2 (by norm_num)), s5cGens, arr5_get3]
    exact s5cTab_eq (by norm_num)
  · rw [Nat.eq_of_beq_eq_true (allN_spec h.2 3 (by norm_num)), s5cGens, arr5_get4]
    exact s5cTab_eq (by norm_num)
  · omega

theorem s5_permG : ∀ k < S5.ng, permOK 100 7 (mask 7) (100 * 7) (S5.G k)
    (pinvS 100 7 (mask 7) (S5.G k)) = true := by
  have h := S5.gensF
  rw [Bool.and_eq_true] at h
  intro k hk
  have hk5 : k < 5 := hk
  rcases k with _ | k
  · rw [Nat.eq_of_beq_eq_true h.1]
    exact allN_spec permF 4 (by norm_num)
  · rw [Nat.eq_of_beq_eq_true (allN_spec h.2 k (by omega))]
    exact allN_spec S5.permS k (by omega)

theorem s5_enumOK : enumOK 100 s5cGens hs100FiveKeys s5cCert = true := by
  unfold s5cCert
  rw [hsKeys]
  exact enumOK_of_bfsK_base s5_gens.1 s5_gens.2 s5_permG S5.ok (by decide) S5.keys (by decide)

theorem s5_size : s5cCert.pts.size = 600 := by
  unfold s5cCert
  rw [hsKeys, enumBfs_pts_base s5_gens.1 s5_gens.2 S5.ok (by decide) S5.keys (by decide),
    Array.size_ofFn]
  exact Nat.eq_of_beq_eq_true S5.card

theorem c2_get {i : ℕ} (hi : i < C2.N) : hs100FiveC2Cert.pts[i]! = unpack 100 7 (C2.T i) := by
  rw [c2_pts, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem s5_mem {i : ℕ} (hi : i < 4) :
    (validA 100 s5cS[i]! && hs100FiveC2Cert.pts.toList.any (eqA 100 s5cS[i]!)) = true := by
  rw [s5cS_eq hi, Bool.and_eq_true]
  refine ⟨CFSG.KC.BfsPin.validA_unpack (allN_spec S5.permS i hi), ?_⟩
  rw [CFSG.KC.Misc.ArrEnum.any_eqA_unpack hw (by rw [c2_pts, Array.size_ofFn]) (fun j hj => c2_get hj)
    (fun j hj => permB_of_pp (c2_pp j hj)) (permB_of_pp (ppSC hi))]
  exact allN_spec S5.memS i hi

theorem cox_parts : (allN 4 fun i => Nat.beq (cm (SC.F i) (SC.F i)) (pidn 100 7)) = true ∧
    (allN 3 fun i => Nat.beq (cm (cm (SC.F i) (SC.F (i + 1))) (SC.F i))
      (cm (cm (SC.F (i + 1)) (SC.F i)) (SC.F (i + 1)))) = true ∧
    (allN 4 fun i => allN 4 fun j => decide (j < i + 2) ||
      Nat.beq (cm (SC.F i) (SC.F j)) (cm (SC.F j) (SC.F i))) = true := by
  have h := S5.cox
  unfold coxK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cox : s5cCoxeterOK = true := by
  obtain ⟨h1, h2, h3⟩ := cox_parts
  unfold s5cCoxeterOK
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi j hj => ?_⟩
  · rw [s5cS_eq hi, compA_PP (ppSC hi) (ppSC hi), idA_eq hw,
      eqA_PP ((ppSC hi).mul (ppSC hi)) (PP.id hw)]
    exact allN_spec h1 i hi
  · have hi' : i + 1 < 4 := by omega
    have p0 := ppSC (i := i) (by omega)
    have p1 := ppSC hi'
    rw [s5cS_eq (by omega), s5cS_eq hi', compA_PP p0 p1, compA_PP (p0.mul p1) p0,
      compA_PP p1 p0, compA_PP (p1.mul p0) p1, eqA_PP ((p0.mul p1).mul p0) ((p1.mul p0).mul p1)]
    exact allN_spec h2 i hi
  · have hij := allN_spec (allN_spec h3 i hi) j hj
    rw [s5cS_eq hi, s5cS_eq hj, compA_PP (ppSC hi) (ppSC hj), compA_PP (ppSC hj) (ppSC hi),
      eqA_PP ((ppSC hi).mul (ppSC hj)) ((ppSC hj).mul (ppSC hi))]
    exact hij

theorem s5cOK_eq : s5cOK = true := by
  unfold s5cOK
  rw [s5_enumOK, s5_size, cox, allLt_iff.2 fun i hi => s5_mem hi]
  rfl

end CertificateChecks.KernelHS100

end
