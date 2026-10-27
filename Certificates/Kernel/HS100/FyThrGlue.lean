module

public import Certificates.Kernel.HS100.FyThrChecks
public import Certificates.Kernel.HS100.FyThrT0
public import Certificates.Kernel.HS100.FyThrT1
public import Certificates.Kernel.HS100.FyThrT2
public import Certificates.Kernel.HS100.FyThrT3
public import Certificates.Kernel.HS100.FyThrT4
public import Certificates.Kernel.HS100.FyThrT5
public import Certificates.Kernel.HS100.FyThrT6
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Co3Five.TailSound
public import CFSG.Certificates.Kernel.Misc.ChainTailQSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ChainTailSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.EvenSporadicStandard.TwoHS CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
open CFSG.RankThree.Native CFSG.Certificates.Native

#kc_forall_chunks fyAll (fun k => fyBr k = true) 77 CertificateChecks.KernelHS100.fyBr 1

theorem fyTab_eq {k : ℕ} (hk : k < 13) : fyThrTab k = unpack 100 7 (FT.F k) := by
  rw [fyThrTab, FT.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound FT.all k hk

theorem ppFT {j : ℕ} (hj : j < 13) : PP 100 7 (FT.F j) := PP_of_permOK hw (allN_spec Fy.perm j hj)

theorem siftFT {j : ℕ} (hj : j < 10) :
    siftA 100 hs100PLevels hs100BaseArr 0 (unpack 100 7 (FT.F j)) = true :=
  siftP rfl (allN_spec Fy.sift j hj)

theorem fyX : fyThrX = unpack 100 7 (FT.F 0) := fyTab_eq (by norm_num)

theorem fyKeys : fyThrKeys = [0, 1, 2, 3, 4] := rfl

theorem fyGens : Nat.beq (FQ.G 0) (FT.F 0) = true ∧ Nat.beq (FQ.G 1) (FT.F 1) = true ∧
    (allN 3 fun k => Nat.beq (FE.G k) (FT.F (k + 10))) = true := by
  have h := Fy.gens
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fq_gens : fyThrQGens.size = FQ.ng ∧
    ∀ k < FQ.ng, fyThrQGens[k]! = unpack 100 7 (FQ.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true fyGens.1]
    exact fyTab_eq (by norm_num)
  · rw [Nat.eq_of_beq_eq_true fyGens.2.1]
    exact fyTab_eq (by norm_num)

theorem fq_perm : ∀ k < FQ.ng, permOK 100 7 (mask 7) (100 * 7) (FQ.G k)
    (pinvS 100 7 (mask 7) (FQ.G k)) = true := by
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true fyGens.1]
    exact allN_spec Fy.perm 0 (by norm_num)
  · rw [Nat.eq_of_beq_eq_true fyGens.2.1]
    exact allN_spec Fy.perm 1 (by norm_num)

theorem fe_gens : fyThrCGens.size = FE.ng ∧
    ∀ k < FE.ng, fyThrCGens[k]! = unpack 100 7 (FE.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk3 : k < 3 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec fyGens.2.2 k hk3)]
  interval_cases k
  · exact fyTab_eq (by norm_num)
  · exact fyTab_eq (by norm_num)
  · exact fyTab_eq (by norm_num)

theorem fe_perm : ∀ k < FE.ng, permOK 100 7 (mask 7) (100 * 7) (FE.G k)
    (pinvS 100 7 (mask 7) (FE.G k)) = true := by
  intro k hk
  have hk3 : k < 3 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec fyGens.2.2 k hk3)]
  exact allN_spec Fy.perm _ (by omega)

theorem fq_pts : fyThrQCert.pts = Array.ofFn (n := FQ.N) fun i => unpack 100 7 (FQ.T i.val) := by
  unfold fyThrQCert
  rw [fyKeys]
  exact enumBfs_pts_base fq_gens.1 fq_gens.2 FQ.ok (by decide) FQ.keys (by decide)

theorem fq_enumOK : enumOK 100 fyThrQGens fyThrKeys fyThrQCert = true := by
  unfold fyThrQCert
  rw [fyKeys]
  exact enumOK_of_bfsK_base fq_gens.1 fq_gens.2 fq_perm FQ.ok (by decide) FQ.keys (by decide)

theorem fe_list : fyThrE = (List.range FE.N).map fun e => unpack 100 7 (FE.T e) := by
  unfold fyThrE
  rw [fyKeys, enumBfs_pts_base fe_gens.1 fe_gens.2 FE.ok (by decide) FE.keys (by decide)]
  exact pts_toList (N := FE.N) fun e => unpack 100 7 (FE.T e)

theorem fySizes : FQ.N = 9 ∧ FE.N = 36 := by
  have h := Fy.sizes
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem fyLev : fyThrLevels = rawLevels 100 hs100StrongArrs hs100BaseArr := rfl

theorem fyTail : tailOK 100 fyThrLevels fyThrX fyThrE 4 1 (idA 100) = true := by
  have hb : ∀ k < rcnt (HC.LR 1), fyBr k = true := by
    rw [Nat.eq_of_beq_eq_true Fy.rc]
    exact fyAll
  have hk : ptailK 100 7 HC.LR HC.TR HC.BP (FT.F 0) (fun _ => 0) [] FE.N FE.T 4 1
      (pidn 100 7) = true := by
    have e : ptailK 100 7 HC.LR HC.TR HC.BP (FT.F 0) (fun _ => 0) [] FE.N FE.T (3 + 1) 1
        (pidn 100 7) = strictB (HC.LR 1) fun R => allN (rcnt R) fun k =>
          !(relOKK 7 (mask 7) HC.BP (fun _ => 0) [] 1 (pidn 100 7) (rpt 7 (mask 7) R k)) ||
            ptailK 100 7 HC.LR HC.TR HC.BP (FT.F 0) (fun _ => 0) [] FE.N FE.T 3 2
              (pcomp 100 7 (mask 7) (pidn 100 7) (HC.TR (roff 100 (100 * 7) R + k))) := rfl
    rw [e, CFSG.KS.Raw.strictB_eq]
    refine allN_intro fun k hk' => ?_
    have hr : relOKK 7 (mask 7) HC.BP (fun _ => 0) [] 1 (pidn 100 7) (rpt 7 (mask 7) (HC.LR 1) k) =
        true := rfl
    rw [hr, Bool.not_true, Bool.false_or]
    exact ptailK_of_ptailQ (ppFT (by norm_num)) (by norm_num) (by norm_num) 2 2 _ (hb k hk')
  have hEp : ∀ e < FE.N, permB 100 7 (FE.T e) = true :=
    fun e he => permB_of_pp (PP_pts FE.ok fe_perm e he)
  have hag : Ag 100 7 (idA 100) (pidn 100 7) := by
    rw [idA_eq hw]
    exact ag_unpack 100 7 _
  rw [fyLev]
  exact tailOK_of_ptailK binds HC.perm HC.hl hw fyX (permB_of_pp (ppFT (by norm_num))) (fun _ => 0)
    fe_list hEp 4 1 rfl (idA 100) (pidn 100 7) (PP.id hw) hag hk

theorem fyCent : fyThrCentOK = true := by
  have hv : validA 100 fyThrX = true := by
    rw [fyX]
    exact CFSG.KC.BfsPin.validA_unpack (allN_spec Fy.perm 0 (by norm_num))
  have h0 : (fyThrX[0]! == 0) = true := by
    rw [fyX, CFSG.KC.BfsPin.unpack_getElem!, if_pos (by norm_num), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true Fy.fix0
  have hf : (fixLevCount 100 fyThrLevels fyThrX 0 == 10) = true := by
    rw [fyLev, fyX, fixLevCount_eq binds HC.perm HC.hl (i := 0) (by norm_num) (FT.F 0), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true Fy.fixCnt
  have hl : (fyThrE.length == 36) = true := by
    rw [fe_list, List.length_map, List.length_range, fySizes.2]
    rfl
  unfold fyThrCentOK
  rw [hv, h0, hf, hl, fyTail]
  rfl

theorem fySift : allLt fyThrQGens.size
    (fun k => siftA 100 fyThrLevels hs100BaseArr 0 fyThrQGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := hk
  rw [fq_gens.2 k hk2]
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true fyGens.1]
    exact siftFT (by norm_num)
  · rw [Nat.eq_of_beq_eq_true fyGens.2.1]
    exact siftFT (by norm_num)

theorem fyTrans_mem {j : ℕ} (hj : j < 8) : fyThrTab (j + 2) ∈ fyThrTrans :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem fyPt {k : ℕ} (hk : k < 9) : (eqA 100 (unpack 100 7 (FQ.T k)) (idA 100) ||
    fyThrTrans.any fun g => validA 100 g && siftA 100 fyThrLevels hs100BaseArr 0 g &&
      eqA 100 (compA 100 g fyThrX) (compA 100 (unpack 100 7 (FQ.T k)) g)) = true := by
  have hkN : k < FQ.N := by rw [fySizes.1]; exact hk
  have hT : PP 100 7 (FQ.T k) := PP_pts FQ.ok fq_perm k hkN
  have h := allN_spec Fy.trans k hk
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨h8, h⟩ := h
  have h8' : FW k < 8 := Nat.blt_eq ▸ h8
  rw [Bool.or_eq_true]
  rcases h with h | h
  · left
    rw [idA_eq hw, eqA_PP hT (PP.id hw)]
    exact h
  · right
    rw [List.any_eq_true]
    refine ⟨fyThrTab (FW k + 2), fyTrans_mem h8', ?_⟩
    have hg : PP 100 7 (FT.F (FW k + 2)) := ppFT (by omega)
    have p0 : PP 100 7 (FT.F 0) := ppFT (by norm_num)
    rw [fyTab_eq (by omega), fyX, compA_PP hg p0, compA_PP hT hg, eqA_PP (hg.mul p0) (hT.mul hg),
      Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨CFSG.KC.BfsPin.validA_unpack (allN_spec Fy.perm _ (by omega)), siftFT (by omega)⟩, h⟩

theorem fyFuse : fyThrFuseOK = true := by
  have hs : (fyThrQCert.pts.size == 9) = true := by
    rw [fq_pts, Array.size_ofFn, fySizes.1]
    rfl
  have ht : (fyThrQCert.pts.toList.all fun z => eqA 100 z (idA 100) ||
      fyThrTrans.any fun g => validA 100 g && siftA 100 fyThrLevels hs100BaseArr 0 g &&
        eqA 100 (compA 100 g fyThrX) (compA 100 z g)) = true := by
    rw [fq_pts, pts_toList (N := FQ.N) fun e => unpack 100 7 (FQ.T e), List.all_map,
      List.all_eq_true]
    intro k hk
    have hk9 : k < 9 := by rw [← fySizes.1]; exact List.mem_range.1 hk
    exact fyPt hk9
  unfold fyThrFuseOK
  rw [fq_enumOK, hs, fySift, ht]
  rfl

theorem fyThr : fyThrOK = true := by
  unfold fyThrOK
  rw [fyCent, fyFuse]
  rfl

end CertificateChecks.KernelHS100

end
