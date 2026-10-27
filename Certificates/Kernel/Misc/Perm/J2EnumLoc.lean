module

public import Certificates.Kernel.Misc.Perm.J2LocK2
public import Certificates.Kernel.Misc.Perm.J2EnumS
public import CFSG.Certificates.Kernel.Misc.SetCodesSound
public import CFSG.Certificates.Kernel.Misc.EnumBfsMem
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw cm X Y I all_of_chunks lt_of)
open CertificateChecks.KernelMisc.J2Fam (R rV1 rV2 GA GV H1 HV pGV pHV memVK V1 V2)
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.EnumBfs (enumBfs_mem any_congr_of_mem allLt_congr_of_mem)

#kc_forall_chunks caCS (fun c => caC c = true) 1 CertificateChecks.KernelMisc.J2En.caC 1
#kc_forall_chunks naCS (fun c => naC c = true) 1 CertificateChecks.KernelMisc.J2En.naC 1
#kc_forall_chunks nvCS (fun c => nvC c = true) 8 CertificateChecks.KernelMisc.J2En.nvC 1

theorem caAll : ∀ k < 36, caK (lget CaP k) = true := all_of_chunks 36 1 caCS

theorem naAll : ∀ k < 72, naK (lget NaP k) = true := all_of_chunks 72 1 naCS

theorem nvAll : ∀ k < 720, nvK (lget NVP k) = true := all_of_chunks 90 8 nvCS

theorem memCCa : ∀ x, x ∈ cCa.pts ↔ x ∈ cCaL.pts := by
  unfold cCa
  exact enumBfs_mem enumCa (by rw [sizeCa]; norm_num)

theorem memCNa : ∀ x, x ∈ cNa.pts ↔ x ∈ cNaL.pts := by
  unfold cNa
  exact enumBfs_mem enumNa (by rw [sizeNa]; norm_num)

theorem memCNV : ∀ x, x ∈ cNV.pts ↔ x ∈ cNVL.pts := by
  unfold cNV
  exact enumBfs_mem enumNV (by rw [sizeNV]; norm_num)

theorem rCaL {k : ℕ} (hk : k < 36) : R cCaL.pts[k]! (lget CaP k) :=
  ⟨(certL_bound 36 2 CaP CaE CaR CaL).2.1 k hk, ptPerm (N := 36) (all_of_chunks 36 1 ptCaS) k hk⟩

theorem rNaL {k : ℕ} (hk : k < 72) : R cNaL.pts[k]! (lget NaP k) :=
  ⟨(certL_bound 72 3 NaP NaE NaR NaL).2.1 k hk, ptPerm (N := 72) (all_of_chunks 72 1 ptNaS) k hk⟩

theorem rNVL {k : ℕ} (hk : k < 720) : R cNVL.pts[k]! (lget NVP k) :=
  ⟨(certL_bound 720 3 NVP NVE NVR NVL).2.1 k hk,
    ptPerm (N := 720) (all_of_chunks 90 8 ptNVS) k hk⟩

theorem inCa {t : Array ℕ} {p : ℕ} (ht : R t p) : inCert cCa t = memK 36 (lget CaP) p := by
  unfold inCert
  rw [any_congr_of_mem memCCa, ht.1]
  exact any_eqA_unpack hw (certL_bound 36 2 CaP CaE CaR CaL).1
    (certL_bound 36 2 CaP CaE CaR CaL).2.1 (fun i hi => (rCaL hi).2) ht.2

theorem hO3 : o3Sets.size = 3 ∧ ∀ i < 3, o3Sets[i]! = unpack 1 9 (O3 i) :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), fun i hi => by
    interval_cases i <;> exact arrBind_sound (by quickRfl)⟩

theorem hB4 : b4Sets.size = 4 ∧ ∀ i < 4, b4Sets[i]! = unpack 3 9 (B4 i) :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), fun i hi => by
    interval_cases i <;> exact arrBind_sound (by quickRfl)⟩

theorem hO3lt : ∀ i < 3, ∀ q < 1, pg 9 (mask 9) (O3 i) q < 315 := lt_of (by quickRfl)

theorem hB4lt : ∀ i < 4, ∀ q < 3, pg 9 (mask 9) (B4 i) q < 315 := lt_of (by quickRfl)

theorem gnvL : gensNVArr.toList = [GV 0, GV 1, HV].map (unpack 315 9) := by
  apply List.ext_getElem
  · simp [gnv_size]
  · intro k h1 _
    have hk : k < 3 := by simpa [gnv_size] using h1
    rw [Array.getElem_toList, ← getElem!_pos gensNVArr k (by simpa using h1), hgNV k hk]
    interval_cases k <;> rfl

theorem pNV : ∀ n ∈ [GV 0, GV 1, HV], permB 315 9 n = true := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact pGV 0 (by norm_num)
  · exact pGV 1 (by norm_num)
  · exact pHV

theorem twoTestU {gs : Array (Array ℕ)} {ns : List ℕ} (hg : gs.toList = ns.map (unpack 315 9))
    (hn : ∀ n ∈ ns, permB 315 9 n = true) {t : Array ℕ} {p : ℕ} (ht : R t p) :
    twoTest gs t = twoGK ns p := by
  obtain ⟨rfl, hp⟩ := ht
  unfold twoTest twoGK
  rw [← Array.all_toList, hg, J2Fam.R.two ⟨rfl, hp⟩,
    all_map_congr (g := fun n => two7K (cm p (cj n p))) fun n hm => by
      rw [conjU (hn n hm) hp, compU hp (pcj (hn n hm) hp)]
      exact J2Fam.R.two ⟨rfl, pcm hp (pcj (hn n hm) hp)⟩]
  rfl

theorem memVK_eq (p : ℕ) : memVK p = memL VEK p := by
  simp only [memVK, memL, VEK, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem caTwo_lit :
    (allLt cCaL.pts.size fun k => !(isTwoA cCaL.pts[k]!) || inV cCaL.pts[k]!) = true := by
  rw [allLt_iff, sizeCa]
  intro k hk
  rw [(rCaL hk).two, (rCaL hk).memV, memVK_eq]
  exact caAll k hk

theorem caTwo : (allLt cCa.pts.size fun k => !(isTwoA cCa.pts[k]!) || inV cCa.pts[k]!) = true :=
  (allLt_congr_of_mem memCCa fun t => !(isTwoA t) || inV t).trans caTwo_lit

theorem v1Ca : inCert cCa v1Arr = true := by
  rw [inCa rV1]
  quickRfl

theorem v2Ca : inCert cCa v2Arr = true := by
  rw [inCa rV2]
  quickRfl

theorem v12c : commA v1Arr v2Arr = true := by
  rw [rV1.commA rV2]
  quickRfl

theorem v1sq : eqA 315 (compA 315 v1Arr v1Arr) (idA 315) = true := by
  rw [(rV1.comp rV1).eq J2Fam.R.id]
  quickRfl

theorem v2sq : eqA 315 (compA 315 v2Arr v2Arr) (idA 315) = true := by
  rw [(rV2.comp rV2).eq J2Fam.R.id]
  quickRfl

theorem v1ne : (!(eqA 315 v1Arr (idA 315))) = true := by
  rw [rV1.eq J2Fam.R.id]
  quickRfl

theorem v2ne : (!(eqA 315 v2Arr (idA 315))) = true := by
  rw [rV2.eq J2Fam.R.id]
  quickRfl

theorem v12ne : (!(eqA 315 v1Arr v2Arr)) = true := by
  rw [rV1.eq rV2]
  quickRfl

theorem o3sz : (o3Sets.size == 3) = true := by
  rw [hO3.1]
  rfl

theorem b4sz : (b4Sets.size == 4) = true := by
  rw [hB4.1]
  rfl

theorem o3ok : setsOK o3Sets 1 = true := by
  rw [setsOK_sound hO3]
  quickRfl

theorem b4ok : setsOK b4Sets 3 = true := by
  rw [setsOK_sound hB4]
  quickRfl

theorem naSet_lit : (allLt cNaL.pts.size fun k => permutesSets o3Sets cNaL.pts[k]! &&
    permutesSets b4Sets cNaL.pts[k]! &&
    (!(fixesSets o3Sets cNaL.pts[k]! && fixesSets b4Sets cNaL.pts[k]!) ||
      eqA 315 cNaL.pts[k]! (idA 315))) = true := by
  rw [allLt_iff, sizeNa]
  intro k hk
  have r := rNaL hk
  rw [r.eq J2Fam.R.id, r.1, permutes_sound hO3 hO3lt, permutes_sound hB4 hB4lt, fixes_sound hO3 hO3lt,
    fixes_sound hB4 hB4lt]
  have h := naAll k hk
  unfold naK at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem naSet : (allLt cNa.pts.size fun k => permutesSets o3Sets cNa.pts[k]! &&
    permutesSets b4Sets cNa.pts[k]! &&
    (!(fixesSets o3Sets cNa.pts[k]! && fixesSets b4Sets cNa.pts[k]!) ||
      eqA 315 cNa.pts[k]! (idA 315))) = true :=
  (allLt_congr_of_mem memCNa fun t => permutesSets o3Sets t && permutesSets b4Sets t &&
    (!(fixesSets o3Sets t && fixesSets b4Sets t) || eqA 315 t (idA 315))).trans naSet_lit

theorem naActs : (allLt gensNaArr.size fun k => actsBy o3Sets gensNaArr[k]! (sig3.getD k []) &&
    actsBy b4Sets gensNaArr[k]! (sig4.getD k [])) = true := by
  rw [allLt_iff, gna_size]
  intro k hk
  have h3 : ∀ i < 3, (sig3.getD k []).getD i 0 < 3 := by interval_cases k <;> decide
  have h4 : ∀ i < 4, (sig4.getD k []).getD i 0 < 4 := by interval_cases k <;> decide
  rw [hgNa k hk, acts_sound hO3 hO3lt h3, acts_sound hB4 hB4lt h4]
  interval_cases k <;> quickRfl

theorem naTwo_lit :
    (allLt cNaL.pts.size fun k => !(twoTest gensNaArr cNaL.pts[k]!) || inV cNaL.pts[k]!) =
      true := by
  rw [allLt_iff, sizeNa]
  intro k hk
  have r := rNaL hk
  rw [twoTestU gnaL pNa r, r.memV, memVK_eq]
  have h := naAll k hk
  unfold naK at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem naTwo :
    (allLt cNa.pts.size fun k => !(twoTest gensNaArr cNa.pts[k]!) || inV cNa.pts[k]!) = true :=
  (allLt_congr_of_mem memCNa fun t => !(twoTest gensNaArr t) || inV t).trans naTwo_lit

theorem nvTwo_lit :
    (allLt cNVL.pts.size fun k => !(twoTest gensNVArr cNVL.pts[k]!) || inV cNVL.pts[k]!) =
      true := by
  rw [allLt_iff, sizeNV]
  intro k hk
  have r := rNVL hk
  rw [twoTestU gnvL pNV r, r.memV, memVK_eq]
  exact nvAll k hk

theorem nvTwo :
    (allLt cNV.pts.size fun k => !(twoTest gensNVArr cNV.pts[k]!) || inV cNV.pts[k]!) = true :=
  (allLt_congr_of_mem memCNV fun t => !(twoTest gensNVArr t) || inV t).trans nvTwo_lit

theorem outer : (allLt cNa.pts.size fun k =>
    !(twoTest8 gensNaArr (compA 315 cNa.pts[k]! (compA 315 p0Arr outerArr)))) = true :=
  (allLt_congr_of_mem memCNa fun t =>
    !(twoTest8 gensNaArr (compA 315 t (compA 315 p0Arr outerArr)))).trans outer_lit

theorem chkLocal45_true : chkLocal45 = true := by
  unfold chkLocal45
  rw [caTwo, v1Ca, v2Ca, v12c, v1sq, v2sq, v1ne, v2ne, v12ne, o3sz, o3ok, b4sz, b4ok, naSet,
    naActs, naTwo, nvTwo, outer0_true, outer]
  rfl

theorem neg_caV : (!(!(two7K V2) || memL [I, V1] V2)) = true := by quickRfl

theorem neg_nvV : (!(!(twoGK [GV 0, GV 1, HV] V1) || memL [I, V2, cm V1 V2] V1)) = true := by
  quickRfl

theorem neg_setY : (!(naSetK Y)) = true := by quickRfl

theorem neg_acts : (!(actsK 3 1 9 O3 H1 fun i => [1, 2, 0].getD i 0)) = true := by quickRfl

end CertificateChecks.KernelMisc.J2En

end
