module

public import Certificates.Kernel.HS100.S5OChecks
public import Certificates.Kernel.HS100.S5OCChecks
public import Certificates.Kernel.HS100.FyThrChecks
public import Certificates.Kernel.HS100.S5OT0
public import Certificates.Kernel.HS100.S5OT1
public import Certificates.Kernel.HS100.S5OT2
public import Certificates.Kernel.HS100.S5OT3
public import Certificates.Kernel.HS100.S5OT4
public import Certificates.Kernel.HS100.S5OT5
public import Certificates.Kernel.HS100.S5OT6
public import Certificates.Kernel.HS100.S5OZ0
public import Certificates.Kernel.HS100.S5OZ1
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Co3Five.TailSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.RawSiftKConv
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ChainTailSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.EvenSporadicStandard.HSStd CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
open CFSG.RankThree.Native CFSG.Certificates.Native

#kc_forall_chunks s5oBrAll (fun k => s5oBr k = true) 77 CertificateChecks.KernelHS100.s5oBr 1

#kc_forall_chunks zcAll (fun b => zcBlk b = true) 24 CertificateChecks.KernelHS100.zcBlk 1

theorem oTab_eq {k : ℕ} (hk : k < 16) : s5oTab k = unpack 100 7 (OX.F k) := by
  rw [s5oTab, OX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound OX.all k hk

theorem ppO {j : ℕ} (hj : j < 16) : PP 100 7 (OX.F j) := PP_of_permOK hw (allN_spec S5O.perm j hj)

theorem ppU : PP 100 7 (HP.F 15) := PP_of_permOK hw S5O.permU

theorem s5U_eq : s5U = unpack 100 7 (HP.F 15) := hs100Arr_eq 15 (by norm_num)

theorem validO {j : ℕ} (hj : j < 16) : validA 100 (unpack 100 7 (OX.F j)) = true :=
  CFSG.KC.BfsPin.validA_unpack (allN_spec S5O.perm j hj)

theorem inP_of {G : ℕ} (hr : rngK G = true) (h : inHS G = true) : s5InP (unpack 100 7 G) = true := by
  unfold s5InP s5Levels
  exact siftP rfl (by rw [Bool.and_eq_true]; exact ⟨hr, h⟩)

theorem notP_of {G : ℕ} (hr : rngK G = true) (h : inHS G = false) :
    s5InP (unpack 100 7 G) = false := by
  unfold rngK at hr
  rw [Bool.and_eq_true] at hr
  unfold s5InP s5Levels
  exact Orb.siftA_false_of_K binds HC.perm HC.hl hw (Nat.eq_of_beq_eq_true hr.1) hr.2 h

theorem compO {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) :
    compA 100 (unpack 100 7 p) (unpack 100 7 q) = unpack 100 7 (pm p q) := compA_PP hp hq

theorem eqO {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) :
    eqA 100 (unpack 100 7 p) (unpack 100 7 q) = Nat.beq p q := eqA_PP hp hq

theorem ppm {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) : PP 100 7 (pm p q) := hp.mul hq

theorem s5Keys5 : s5Keys = [0, 1, 2, 3, 4] := rfl

theorem s5oGensO : (allN 4 fun k => Nat.beq (OS.G k) (OX.F k)) = true ∧
    (allN 2 fun k => Nat.beq (OE.G k) (OX.F (k + 14))) = true := by
  have h := S5O.gens
  rw [Bool.and_eq_true] at h
  exact h

theorem sgen_eq {k : ℕ} (hk : k < 4) : s5oSGens[k]! = unpack 100 7 (OX.F k) := by
  interval_cases k
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)

theorem xgen_eq {k : ℕ} (hk : k < 7) : s5oXs[k]! = unpack 100 7 (OX.F (k + 7)) := by
  interval_cases k
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)

theorem os_gens : s5oSGens.size = OS.ng ∧ ∀ k < OS.ng, s5oSGens[k]! = unpack 100 7 (OS.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec s5oGensO.1 k hk4)]
  exact sgen_eq hk4

theorem os_perm : ∀ k < OS.ng, permOK 100 7 (mask 7) (100 * 7) (OS.G k)
    (pinvS 100 7 (mask 7) (OS.G k)) = true := by
  intro k hk
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec s5oGensO.1 k hk4)]
  exact allN_spec S5O.perm k (by omega)

theorem oe_gens : s5oCGens.size = OE.ng ∧ ∀ k < OE.ng, s5oCGens[k]! = unpack 100 7 (OE.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec s5oGensO.2 k hk2)]
  interval_cases k
  · exact oTab_eq (by norm_num)
  · exact oTab_eq (by norm_num)

theorem oe_perm : ∀ k < OE.ng, permOK 100 7 (mask 7) (100 * 7) (OE.G k)
    (pinvS 100 7 (mask 7) (OE.G k)) = true := by
  intro k hk
  have hk2 : k < 2 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec s5oGensO.2 k hk2)]
  exact allN_spec S5O.perm _ (by omega)

theorem oc_gens : s5oXs.size = OC.ng ∧ ∀ k < OC.ng, s5oXs[k]! = unpack 100 7 (OC.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk7 : k < 7 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec OC.gensX k hk7)]
  exact xgen_eq hk7

theorem oc_perm : ∀ k < OC.ng, permOK 100 7 (mask 7) (100 * 7) (OC.G k)
    (pinvS 100 7 (mask 7) (OC.G k)) = true := by
  intro k hk
  have hk7 : k < 7 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec OC.gensX k hk7)]
  exact allN_spec S5O.perm _ (by omega)

theorem os_pts : s5oSCert.pts = Array.ofFn (n := OS.N) fun i => unpack 100 7 (OS.T i.val) := by
  unfold s5oSCert
  rw [s5Keys5]
  exact enumBfs_pts_base os_gens.1 os_gens.2 OS.ok (by decide) OS.keys (by decide)

theorem os_enumOK : enumOK 100 s5oSGens s5Keys s5oSCert = true := by
  unfold s5oSCert
  rw [s5Keys5]
  exact enumOK_of_bfsK_base os_gens.1 os_gens.2 os_perm OS.ok (by decide) OS.keys (by decide)

theorem oc_pts : s5oXCert.pts = Array.ofFn (n := OC.N) fun i => unpack 100 7 (OC.T i.val) := by
  unfold s5oXCert
  rw [s5Keys5]
  exact enumBfs_pts_base oc_gens.1 oc_gens.2 OC.ok (by decide) OC.keys (by decide)

theorem oc_enumOK : enumOK 100 s5oXs s5Keys s5oXCert = true := by
  unfold s5oXCert
  rw [s5Keys5]
  exact enumOK_of_bfsK_base oc_gens.1 oc_gens.2 oc_perm OC.ok (by decide) OC.keys (by decide)

theorem oe_list : s5oE = (List.range OE.N).map fun e => unpack 100 7 (OE.T e) := by
  unfold s5oE
  rw [s5Keys5, enumBfs_pts_base oe_gens.1 oe_gens.2 OE.ok (by decide) OE.keys (by decide)]
  exact pts_toList (N := OE.N) fun e => unpack 100 7 (OE.T e)

theorem oSizes : OS.N = 1024 ∧ OE.N = 1344 ∧ OC.N = 40320 := by
  have h := S5O.sizes
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2, Nat.eq_of_beq_eq_true OC.card⟩

theorem ppOS {k : ℕ} (hk : k < 1024) : PP 100 7 (OS.T k) :=
  PP_pts OS.ok os_perm k (by rw [oSizes.1]; exact hk)

theorem ppOC {k : ℕ} (hk : k < 40320) : PP 100 7 (OC.T k) :=
  PP_pts OC.ok oc_perm k (by rw [oSizes.2.2]; exact hk)

theorem gensP : allLt s5oSGens.size
    (fun k => s5InP s5oSGens[k]! || s5InP (compA 100 s5U s5oSGens[k]!)) = true := by
  rw [allLt_iff]
  intro k hk
  have hk4 : k < 4 := hk
  have h := allN_spec S5O.gensP k hk4
  rw [sgen_eq hk4, s5U_eq, compO ppU (ppO (by omega))]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (inP_of h1 h2)
  · exact Or.inr (inP_of h1 h2)

theorem zParts : rngK (OX.F 4) = true ∧ inHS (OX.F 4) = true ∧
    (!Nat.beq (OX.F 4) (pidn 100 7)) = true ∧ Nat.beq (pm (OX.F 4) (OX.F 4)) (pidn 100 7) = true := by
  have h := S5O.z
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem yParts : rngK (OX.F 5) = true ∧ inHS (OX.F 5) = false ∧
    Nat.beq (pm (OX.F 5) (OX.F 5)) (pidn 100 7) = true ∧ memK 1024 OS.T (OX.F 5) = true ∧
    memK 1024 OS.T (OX.F 6) = true ∧
    Nat.beq (pm (OX.F 6) (OX.F 5)) (pm (pm (OX.F 5) (OX.F 4)) (OX.F 6)) = true := by
  have h := S5O.y
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem os_any {p : ℕ} (hp : PP 100 7 p) :
    s5oSCert.pts.toList.any (eqA 100 (unpack 100 7 p)) = memK 1024 OS.T p := by
  have hN : s5oSCert.pts.size = 1024 := by rw [os_pts, Array.size_ofFn, oSizes.1]
  refine any_eqA_unpack' hw hN (fun i hi => ?_) (fun i hi => permB_of_pp (ppOS hi)) (permB_of_pp hp)
  rw [os_pts, getElem!_pos _ i (by rw [Array.size_ofFn, oSizes.1]; exact hi), Array.getElem_ofFn]

theorem osAll : (s5oSCert.pts.toList.all fun x =>
    !s5InP x || eqA 100 (compA 100 s5oZ x) (compA 100 x s5oZ)) = true := by
  rw [os_pts, pts_toList (N := OS.N) fun e => unpack 100 7 (OS.T e), List.all_map,
    List.all_eq_true]
  intro k hk
  have hk' : k < 1024 := by rw [← oSizes.1]; exact List.mem_range.1 hk
  have h := allN_spec S5O.os k hk'
  unfold osOne at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hr, h⟩ := h
  have hT := ppOS hk'
  have p4 : PP 100 7 (OX.F 4) := ppO (by norm_num)
  rw [Function.comp_apply, s5oZ, oTab_eq (by norm_num), compO p4 hT, compO hT p4,
    eqO (ppm p4 hT) (ppm hT p4)]
  cases hs : inHS (OS.T k)
  · rw [notP_of hr hs]
    rfl
  · rw [hs, Bool.not_true, Bool.false_or] at h
    rw [inP_of hr hs, Bool.not_true, Bool.false_or]
    exact h

theorem xsAll : allLt 7 (fun i => validA 100 s5oXs[i]! && s5InP s5oXs[i]! &&
    eqA 100 (compA 100 s5oXs[i]! s5oY) (compA 100 s5oY s5oXs[i]!)) = true := by
  rw [allLt_iff]
  intro i hi
  have h := allN_spec S5O.xs i hi
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hr, hp⟩, hc⟩ := h
  have px : PP 100 7 (OX.F (i + 7)) := ppO (by omega)
  have p5 : PP 100 7 (OX.F 5) := ppO (by norm_num)
  rw [xgen_eq hi, s5oY, oTab_eq (by norm_num), compO px p5, compO p5 px, eqO (ppm px p5) (ppm p5 px),
    validO (by omega), inP_of hr hp, hc]
  rfl

theorem s5oCoxParts : (allN 7 fun i => Nat.beq (pm (OX.F (i + 7)) (OX.F (i + 7))) (pidn 100 7)) = true ∧
    (allN 6 fun i => Nat.beq (pm (pm (OX.F (i + 7)) (OX.F (i + 8))) (OX.F (i + 7)))
      (pm (pm (OX.F (i + 8)) (OX.F (i + 7))) (OX.F (i + 8)))) = true ∧
    (allN 7 fun i => allN 7 fun j => decide (j < i + 2) ||
      Nat.beq (pm (OX.F (i + 7)) (OX.F (j + 7))) (pm (OX.F (j + 7)) (OX.F (i + 7)))) = true := by
  have h := S5O.cox
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem s5oCox : s5oCoxeterOK = true := by
  obtain ⟨h1, h2, h3⟩ := s5oCoxParts
  unfold s5oCoxeterOK
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi j hj => ?_⟩
  · have p := ppO (j := i + 7) (by omega)
    rw [xgen_eq hi, compO p p, idA_eq hw, eqO (ppm p p) (PP.id hw)]
    exact allN_spec h1 i hi
  · have p0 := ppO (j := i + 7) (by omega)
    have p1 := ppO (j := i + 8) (by omega)
    have e1 : s5oXs[i + 1]! = unpack 100 7 (OX.F (i + 8)) := xgen_eq (by omega)
    rw [xgen_eq (by omega), e1, compO p0 p1, compO (ppm p0 p1) p0, compO p1 p0,
      compO (ppm p1 p0) p1, eqO (ppm (ppm p0 p1) p0) (ppm (ppm p1 p0) p1)]
    exact allN_spec h2 i hi
  · have hij := allN_spec (allN_spec h3 i hi) j hj
    have pi := ppO (j := i + 7) (by omega)
    have pj := ppO (j := j + 7) (by omega)
    rw [xgen_eq hi, xgen_eq hj, compO pi pj, compO pj pi, eqO (ppm pi pj) (ppm pj pi)]
    exact hij

theorem s5oTail : tailOK 100 s5Levels s5oY s5oE 4 1 (idA 100) = true := by
  have hb : ∀ k < rcnt (HC.LR 1), s5oBr k = true := by
    rw [Nat.eq_of_beq_eq_true Fy.rc]
    exact s5oBrAll
  have hk : ptailK 100 7 HC.LR HC.TR HC.BP (OX.F 5) (fun _ => 0) [] OE.N OE.T 4 1
      (pidn 100 7) = true := by
    have e : ptailK 100 7 HC.LR HC.TR HC.BP (OX.F 5) (fun _ => 0) [] OE.N OE.T (3 + 1) 1
        (pidn 100 7) = strictB (HC.LR 1) fun R => allN (rcnt R) fun k =>
          !(relOKK 7 (mask 7) HC.BP (fun _ => 0) [] 1 (pidn 100 7) (rpt 7 (mask 7) R k)) ||
            ptailK 100 7 HC.LR HC.TR HC.BP (OX.F 5) (fun _ => 0) [] OE.N OE.T 3 2
              (pcomp 100 7 (mask 7) (pidn 100 7) (HC.TR (roff 100 (100 * 7) R + k))) := rfl
    rw [e, CFSG.KS.Raw.strictB_eq]
    refine allN_intro fun k hk' => ?_
    have hr : relOKK 7 (mask 7) HC.BP (fun _ => 0) [] 1 (pidn 100 7) (rpt 7 (mask 7) (HC.LR 1) k) =
        true := rfl
    rw [hr, Bool.not_true, Bool.false_or]
    exact hb k hk'
  have hEp : ∀ e < OE.N, permB 100 7 (OE.T e) = true :=
    fun e he => permB_of_pp (PP_pts OE.ok oe_perm e he)
  have hag : Ag 100 7 (idA 100) (pidn 100 7) := by
    rw [idA_eq hw]
    exact ag_unpack 100 7 _
  have hy : s5oY = unpack 100 7 (OX.F 5) := oTab_eq (by norm_num)
  unfold s5Levels
  exact tailOK_of_ptailK binds HC.perm HC.hl hw hy (permB_of_pp (ppO (by norm_num))) (fun _ => 0)
    oe_list hEp 4 1 rfl (idA 100) (pidn 100 7) (PP.id hw) hag hk

theorem cent : s5oCentOK = true := by
  have hy : s5oY = unpack 100 7 (OX.F 5) := oTab_eq (by norm_num)
  have hv : validA 100 s5oY = true := by rw [hy]; exact validO (by norm_num)
  have h0 : (s5oY[0]! == 0) = true := by
    rw [hy, CFSG.KC.BfsPin.unpack_getElem!, if_pos (by norm_num), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true S5O.fix0
  have hf : (fixLevCount 100 s5Levels s5oY 0 == 30) = true := by
    unfold s5Levels
    rw [hy, fixLevCount_eq binds HC.perm HC.hl (i := 0) (by norm_num) (OX.F 5), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true S5O.fixCnt
  have hl : (s5oE.length == 1344) = true := by
    rw [oe_list, List.length_map, List.length_range, oSizes.2.1]
    rfl
  unfold s5oCentOK
  rw [hv, h0, hf, hl, s5oTail]
  rfl

theorem wordProd_eq : ∀ (w : List ℕ), (∀ i ∈ w, i < 7) → ∀ (acc : Array ℕ) (A : ℕ), PP 100 7 A →
    acc = unpack 100 7 A →
    w.foldl (fun acc i => compA 100 acc s5oXs[i]!) acc =
        unpack 100 7 (w.foldl (fun acc i => pm acc (OX.F (i + 7))) A) ∧
      PP 100 7 (w.foldl (fun acc i => pm acc (OX.F (i + 7))) A)
  | [], _, _, _, hA, h => ⟨h, hA⟩
  | i :: w, hw', acc, A, hA, h => by
    have hi : i < 7 := hw' i List.mem_cons_self
    have px := ppO (j := i + 7) (by omega)
    rw [List.foldl_cons, List.foldl_cons]
    refine wordProd_eq w (fun j hj => hw' j (List.mem_cons_of_mem _ hj)) _ _ (ppm hA px) ?_
    rw [h, xgen_eq hi, compO hA px]

theorem zw : s5oZWord.foldl (fun acc i => compA 100 acc s5oXs[i]!) (idA 100) =
      unpack 100 7 (s5oZWord.foldl (fun acc i => pm acc (OX.F (i + 7))) (pidn 100 7)) ∧
    PP 100 7 (s5oZWord.foldl (fun acc i => pm acc (OX.F (i + 7))) (pidn 100 7)) :=
  wordProd_eq s5oZWord (by decide) _ _ (PP.id hw) (idA_eq hw)

theorem zcPt {k : ℕ} (hk : k < 40320) :
    (!eqA 100 (compA 100 s5oZ (unpack 100 7 (OC.T k))) (compA 100 (unpack 100 7 (OC.T k)) s5oZ) ||
      !eqA 100 (s5oPow5 (unpack 100 7 (OC.T k))) (idA 100) ||
      eqA 100 (unpack 100 7 (OC.T k)) (idA 100)) = true := by
  have hT := ppOC hk
  have p4 : PP 100 7 (OX.F 4) := ppO (by norm_num)
  have h0 := zcAll (k / 1680) (Nat.div_lt_of_lt_mul (by omega : k < 1680 * 24))
  unfold zcBlk at h0
  have h := allN_spec h0 (k % 1680) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h
  rw [Nat.div_add_mod] at h
  unfold zcOne pw5 at h
  unfold s5oPow5
  rw [s5oZ, oTab_eq (by norm_num), compO p4 hT, compO hT p4, eqO (ppm p4 hT) (ppm hT p4),
    compO hT hT, compO hT (ppm hT hT), compO hT (ppm hT (ppm hT hT)),
    compO hT (ppm hT (ppm hT (ppm hT hT))), idA_eq hw,
    eqO (ppm hT (ppm hT (ppm hT (ppm hT hT)))) (PP.id hw), eqO hT (PP.id hw)]
  exact h

theorem zok : s5oZOK = true := by
  obtain ⟨hz1, hz2⟩ := zw
  have hzw := S5O.zw
  simp only [Bool.and_eq_true] at hzw
  obtain ⟨⟨e1, e2⟩, e3⟩ := hzw
  have p4 : PP 100 7 (OX.F 4) := ppO (by norm_num)
  have p5 : PP 100 7 (OX.F 5) := ppO (by norm_num)
  have p8 : PP 100 7 (OX.F 8) := ppO (by norm_num)
  have hz : s5oZ = unpack 100 7 (OX.F 4) := oTab_eq (by norm_num)
  have hy : s5oY = unpack 100 7 (OX.F 5) := oTab_eq (by norm_num)
  have w1 : eqA 100 (s5oWordProd s5oZWord) s5oZ = true := by
    unfold s5oWordProd
    rw [hz1, hz, eqO hz2 p4]
    exact e1
  have w2 : eqA 100 (compA 100 s5oXs[1]! s5oZ) (compA 100 s5oZ s5oXs[1]!) = true := by
    rw [xgen_eq (k := 1) (by norm_num), hz, compO p8 p4, compO p4 p8, eqO (ppm p8 p4) (ppm p4 p8)]
    exact e2
  have w3 : eqA 100 (compA 100 s5oZ s5oY) (compA 100 s5oY s5oZ) = true := by
    rw [hz, hy, compO p4 p5, compO p5 p4, eqO (ppm p4 p5) (ppm p5 p4)]
    exact e3
  have w4 : (s5oXCert.pts.toList.all fun a => !eqA 100 (compA 100 s5oZ a) (compA 100 a s5oZ) ||
      !eqA 100 (s5oPow5 a) (idA 100) || eqA 100 a (idA 100)) = true := by
    rw [oc_pts, pts_toList (N := OC.N) fun e => unpack 100 7 (OC.T e), List.all_map,
      List.all_eq_true]
    intro k hk
    have hk' : k < 40320 := by rw [← oSizes.2.2]; exact List.mem_range.1 hk
    exact zcPt hk'
  unfold s5oZOK
  rw [w1, w2, w3, w4]
  rfl

theorem s5o : s5oOK = true := by
  obtain ⟨zr, zh, zn, zz⟩ := zParts
  obtain ⟨yr, yh, yy, ym, sm, sy⟩ := yParts
  have p4 : PP 100 7 (OX.F 4) := ppO (by norm_num)
  have p5 : PP 100 7 (OX.F 5) := ppO (by norm_num)
  have p6 : PP 100 7 (OX.F 6) := ppO (by norm_num)
  have hz : s5oZ = unpack 100 7 (OX.F 4) := oTab_eq (by norm_num)
  have hy : s5oY = unpack 100 7 (OX.F 5) := oTab_eq (by norm_num)
  have hs : s5oS = unpack 100 7 (OX.F 6) := oTab_eq (by norm_num)
  have c1 : (s5oSCert.pts.size == 1024) = true := by
    rw [os_pts, Array.size_ofFn, oSizes.1]
    rfl
  have c2 : validA 100 s5oZ = true := by rw [hz]; exact validO (by norm_num)
  have c3 : s5InP s5oZ = true := by rw [hz]; exact inP_of zr zh
  have c4 : (!eqA 100 s5oZ (idA 100)) = true := by rw [hz, idA_eq hw, eqO p4 (PP.id hw)]; exact zn
  have c5 : eqA 100 (compA 100 s5oZ s5oZ) (idA 100) = true := by
    rw [hz, compO p4 p4, idA_eq hw, eqO (ppm p4 p4) (PP.id hw)]
    exact zz
  have c6 : validA 100 s5oY = true := by rw [hy]; exact validO (by norm_num)
  have c7 : (!s5InP s5oY) = true := by rw [hy, notP_of yr yh]; rfl
  have c8 : eqA 100 (compA 100 s5oY s5oY) (idA 100) = true := by
    rw [hy, compO p5 p5, idA_eq hw, eqO (ppm p5 p5) (PP.id hw)]
    exact yy
  have c9 : s5oSCert.pts.toList.any (eqA 100 s5oY) = true := by rw [hy, os_any p5]; exact ym
  have c10 : validA 100 s5oS = true := by rw [hs]; exact validO (by norm_num)
  have c11 : s5oSCert.pts.toList.any (eqA 100 s5oS) = true := by rw [hs, os_any p6]; exact sm
  have c12 : eqA 100 (compA 100 s5oS s5oY) (compA 100 (compA 100 s5oY s5oZ) s5oS) = true := by
    rw [hs, hy, hz, compO p6 p5, compO p5 p4, compO (ppm p5 p4) p6,
      eqO (ppm p6 p5) (ppm (ppm p5 p4) p6)]
    exact sy
  have c13 : (s5oXCert.pts.size == 40320) = true := by
    rw [oc_pts, Array.size_ofFn, oSizes.2.2]
    rfl
  unfold s5oOK
  rw [os_enumOK, c1, gensP, c2, c3, c4, c5, osAll, c6, c7, c8, c9, c10, c11, c12, xsAll, s5oCox,
    oc_enumOK, c13, cent, zok]
  rfl

end CertificateChecks.KernelHS100

end
