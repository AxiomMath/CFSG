module

public import Certificates.Kernel.Misc.Perm.J2EnumK0
public import Certificates.Kernel.Misc.Perm.J2EnumK1
public import Certificates.Kernel.Misc.Perm.J2LocK0
public import Certificates.Kernel.Misc.Perm.J2LocK1
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.EnumBfsOfOK
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CertificateChecks.KernelMisc.J2C3 (hw hx cm keys_of_all all_of_chunks)
open CertificateChecks.KernelMisc.J2Fam
open CFSG.KC.EnumBfs (enumOK_enumBfs)

#kc_forall_chunks ptCaS (fun c => ptCa c = true) 1 CertificateChecks.KernelMisc.J2En.ptCa 1
#kc_forall_chunks kyCaS (fun c => kyCa c = true) 1 CertificateChecks.KernelMisc.J2En.kyCa 1
#kc_forall_chunks ptNaS (fun c => ptNa c = true) 1 CertificateChecks.KernelMisc.J2En.ptNa 1
#kc_forall_chunks kyNaS (fun c => kyNa c = true) 1 CertificateChecks.KernelMisc.J2En.kyNa 1
#kc_forall_chunks ptCvS (fun c => ptCv c = true) 4 CertificateChecks.KernelMisc.J2En.ptCv 1
#kc_forall_chunks kyCvS (fun c => kyCv c = true) 4 CertificateChecks.KernelMisc.J2En.kyCv 1
#kc_forall_chunks ptNVS (fun c => ptNV c = true) 8 CertificateChecks.KernelMisc.J2En.ptNV 1
#kc_forall_chunks kyNVS (fun c => kyNV c = true) 8 CertificateChecks.KernelMisc.J2En.kyNV 1
#kc_forall_chunks ptNES (fun c => ptNE c = true) 1 CertificateChecks.KernelMisc.J2En.ptNE 1
#kc_forall_chunks kyNES (fun c => kyNE c = true) 1 CertificateChecks.KernelMisc.J2En.kyNE 1
#kc_forall_chunks ptS0S (fun c => ptS0 c = true) 1 CertificateChecks.KernelMisc.J2En.ptS0 1
#kc_forall_chunks kyS0S (fun c => kyS0 c = true) 1 CertificateChecks.KernelMisc.J2En.kyS0 1
#kc_forall_chunks ptS1S (fun c => ptS1 c = true) 1 CertificateChecks.KernelMisc.J2En.ptS1 1
#kc_forall_chunks kyS1S (fun c => kyS1 c = true) 1 CertificateChecks.KernelMisc.J2En.kyS1 1
#kc_forall_chunks ptS2S (fun c => ptS2 c = true) 1 CertificateChecks.KernelMisc.J2En.ptS2 1
#kc_forall_chunks kyS2S (fun c => kyS2 c = true) 1 CertificateChecks.KernelMisc.J2En.kyS2 1
#kc_forall_chunks wCzS (fun c => wCz c = true) 12 CertificateChecks.KernelMisc.J2En.wCz 1
#kc_forall_chunks e0cCzS (fun c => e0cCz c = true) 12 CertificateChecks.KernelMisc.J2En.e0cCz 1
#kc_forall_chunks e0nNZS (fun c => e0nNZ c = true) 24 CertificateChecks.KernelMisc.J2En.e0nNZ 1
#kc_forall_chunks outNaS (fun c => outNa c = true) 1 CertificateChecks.KernelMisc.J2En.outNa 1
#kc_forall_chunks sczSS (fun c => sczS c = true) 1 CertificateChecks.KernelMisc.J2En.sczS 1
#kc_forall_chunks sprodSS (fun c => sprodS c = true) 1 CertificateChecks.KernelMisc.J2En.sprodS 1
#kc_forall_chunks lawCS (fun c => lawC c = true) 4 CertificateChecks.KernelMisc.J2En.lawC 1
#kc_forall_chunks phCS (fun c => phC c = true) 1 CertificateChecks.KernelMisc.J2En.phC 1
#kc_forall_chunks phDCS (fun c => phDC c = true) 1 CertificateChecks.KernelMisc.J2En.phDC 1

theorem certL_bound (N G : ℕ) (P E R L : List ℕ) :
    (certL N G P E R L).pts.size = N ∧
      (∀ i < N, (certL N G P E R L).pts[i]! = unpack 315 9 (lget P i)) ∧
      (∀ i < N, ((certL N G P E R L).edges[i]!).size = G ∧
        ∀ k < G, ((certL N G P E R L).edges[i]!)[k]! = EL G E i k) ∧
      (∀ i < N, (certL N G P E R L).par[i]! = lget R i ∧
        (certL N G P E R L).lab[i]! = lget L i) := by
  refine ⟨by simp [certL], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp [certL, getElem!_pos, hi]
  · have he : (certL N G P E R L).edges[i]! =
        Array.ofFn fun k : Fin G => lget E (G * i + k.val) := by
      simp [certL, getElem!_pos, hi]
    rw [he]
    refine ⟨by simp, fun k hk => ?_⟩
    simp [getElem!_pos, hk]
    rfl
  · simp [certL, getElem!_pos, hi]

theorem hgCa (k : ℕ) (hk : k < 2) : gensCaArr[k]! = unpack 315 9 (GCa k) := by
  interval_cases k
  · exact hga 0 (by norm_num)
  · exact hga 1 (by norm_num)

theorem hgCv (k : ℕ) (hk : k < 2) : gensCvArr[k]! = unpack 315 9 (GCv k) := by
  interval_cases k
  · exact hgv 0 (by norm_num)
  · exact hgv 1 (by norm_num)

theorem push_get {a : Array (Array ℕ)} (ha : a.size = 2) (b : Array ℕ) {k : ℕ} (hk : k < 2) :
    (a.push b)[k]! = a[k]! := by
  rw [getElem!_pos _ k (by simp [ha]; omega), Array.getElem_push_lt (by omega), ← getElem!_pos]

theorem push_last {a : Array (Array ℕ)} (ha : a.size = 2) (b : Array ℕ) : (a.push b)[2]! = b := by
  rw [getElem!_pos _ 2 (by simp [ha])]
  simp [Array.getElem_push, ha]

theorem gna_size : gensNaArr.size = 3 := by simp [gensNaArr, ga_size]
theorem gnv_size : gensNVArr.size = 3 := by simp [gensNVArr, gv_size]

theorem hgNa (k : ℕ) (hk : k < 3) : gensNaArr[k]! = unpack 315 9 (GNa k) := by
  unfold gensNaArr
  interval_cases k
  · rw [push_get ga_size _ (by norm_num)]
    exact hga 0 (by norm_num)
  · rw [push_get ga_size _ (by norm_num)]
    exact hga 1 (by norm_num)
  · rw [push_last ga_size]
    exact hh1

theorem hgNV (k : ℕ) (hk : k < 3) : gensNVArr[k]! = unpack 315 9 (GNV k) := by
  unfold gensNVArr
  interval_cases k
  · rw [push_get gv_size _ (by norm_num)]
    exact hgv 0 (by norm_num)
  · rw [push_get gv_size _ (by norm_num)]
    exact hgv 1 (by norm_num)
  · rw [push_last gv_size]
    exact hhV

theorem gne_size : gensNE.size = 3 := rfl

theorem hgNE (k : ℕ) (hk : k < 3) : gensNE[k]! = unpack 315 9 (GNE k) := by
  interval_cases k
  · exact hx
  · exact hne 0 (by norm_num)
  · exact hne 1 (by norm_num)

theorem hvk (k : ℕ) (hk : k < 3) (i : ℕ) (hi : i = 1 ∨ i = 2) :
    vkArr k i = unpack 315 9 (VK k i) := by
  rcases hi with rfl | rfl
  · unfold vkArr
    rw [if_pos rfl, hcc k hk, hv1, conj_unpack hw (pCC k hk) pV1]
    rfl
  · unfold vkArr
    rw [if_neg (by decide), hcc k hk, hv2, conj_unpack hw (pCC k hk) pV2]
    rfl

theorem gs_size (k : ℕ) : (gensS k).size = 4 := by
  unfold gensS
  split_ifs <;> rfl

theorem hgS0 (j : ℕ) (hj : j < 4) : (gensS 0)[j]! = unpack 315 9 (GS0 j) := by
  interval_cases j
  · exact hvk 0 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 0 (by norm_num) 2 (Or.inr rfl)
  · exact hvk 1 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 1 (by norm_num) 2 (Or.inr rfl)

theorem hgS1 (j : ℕ) (hj : j < 4) : (gensS 1)[j]! = unpack 315 9 (GS1 j) := by
  interval_cases j
  · exact hvk 0 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 0 (by norm_num) 2 (Or.inr rfl)
  · exact hvk 2 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 2 (by norm_num) 2 (Or.inr rfl)

theorem hgS2 (j : ℕ) (hj : j < 4) : (gensS 2)[j]! = unpack 315 9 (GS2 j) := by
  interval_cases j
  · exact hvk 1 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 1 (by norm_num) 2 (Or.inr rfl)
  · exact hvk 2 (by norm_num) 1 (Or.inl rfl)
  · exact hvk 2 (by norm_num) 2 (Or.inr rfl)

theorem enumCa : enumOK 315 gensCaArr keyPts cCaL = true :=
  have b := certL_bound 36 2 CaP CaE CaR CaL
  enumK_sound (G := GCa) hw (by decide) ga_size hgCa b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 36 1 ptCaS) (keys_of_all (all_of_chunks 36 1 kyCaS))

theorem enumNa : enumOK 315 gensNaArr keyPts cNaL = true :=
  have b := certL_bound 72 3 NaP NaE NaR NaL
  enumK_sound (G := GNa) hw (by decide) gna_size hgNa b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 72 1 ptNaS) (keys_of_all (all_of_chunks 72 1 kyNaS))

theorem enumCv : enumOK 315 gensCvArr keyPts cCvL = true :=
  have b := certL_bound 240 2 CvP CvE CvR CvL
  enumK_sound (G := GCv) hw (by decide) gv_size hgCv b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 60 4 ptCvS) (keys_of_all (all_of_chunks 60 4 kyCvS))

theorem enumNV : enumOK 315 gensNVArr keyPts cNVL = true :=
  have b := certL_bound 720 3 NVP NVE NVR NVL
  enumK_sound (G := GNV) hw (by decide) gnv_size hgNV b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 90 8 ptNVS) (keys_of_all (all_of_chunks 90 8 kyNVS))

theorem enumNE : enumOK 315 gensNE keyPts cNEL = true :=
  have b := certL_bound 54 3 NEP NEE NER NEL
  enumK_sound (G := GNE) hw (by decide) gne_size hgNE b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 54 1 ptNES) (keys_of_all (all_of_chunks 54 1 kyNES))

theorem enumS0 : enumOK 315 (gensS 0) keyPts (cSL 0) = true :=
  have b := certL_bound 64 4 S0P S0E S0R S0L
  enumK_sound (G := GS0) hw (by decide) (gs_size 0) hgS0 b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 64 1 ptS0S) (keys_of_all (all_of_chunks 64 1 kyS0S))

theorem enumS1 : enumOK 315 (gensS 1) keyPts (cSL 1) = true :=
  have b := certL_bound 64 4 S1P S1E S1R S1L
  enumK_sound (G := GS1) hw (by decide) (gs_size 1) hgS1 b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 64 1 ptS1S) (keys_of_all (all_of_chunks 64 1 kyS1S))

theorem enumS2 : enumOK 315 (gensS 2) keyPts (cSL 2) = true :=
  have b := certL_bound 64 4 S2P S2E S2R S2L
  enumK_sound (G := GS2) hw (by decide) (gs_size 2) hgS2 b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 64 1 ptS2S) (keys_of_all (all_of_chunks 64 1 kyS2S))

theorem sizeCa : cCaL.pts.size = 36 := (certL_bound 36 2 CaP CaE CaR CaL).1
theorem sizeNa : cNaL.pts.size = 72 := (certL_bound 72 3 NaP NaE NaR NaL).1
theorem sizeCv : cCvL.pts.size = 240 := (certL_bound 240 2 CvP CvE CvR CvL).1
theorem sizeNV : cNVL.pts.size = 720 := (certL_bound 720 3 NVP NVE NVR NVL).1
theorem sizeNE : cNEL.pts.size = 54 := (certL_bound 54 3 NEP NEE NER NEL).1
theorem sizeS0 : (cSL 0).pts.size = 64 := (certL_bound 64 4 S0P S0E S0R S0L).1
theorem sizeS1 : (cSL 1).pts.size = 64 := (certL_bound 64 4 S1P S1E S1R S1L).1
theorem sizeS2 : (cSL 2).pts.size = 64 := (certL_bound 64 4 S2P S2E S2R S2L).1

theorem chkEnum45_true : chkEnum45 = true := by
  have a := enumOK_enumBfs (fuel := 100) enumCa (by rw [sizeCa]; norm_num)
  have b := enumOK_enumBfs (fuel := 200) enumNa (by rw [sizeNa]; norm_num)
  have c := enumOK_enumBfs (fuel := 500) enumCv (by rw [sizeCv]; norm_num)
  have d := enumOK_enumBfs (fuel := 1000) enumNV (by rw [sizeNV]; norm_num)
  have e := enumOK_enumBfs (fuel := 100) enumNE (by rw [sizeNE]; norm_num)
  have s0 := enumOK_enumBfs (fuel := 200) enumS0 (by rw [sizeS0]; norm_num)
  have s1 := enumOK_enumBfs (fuel := 200) enumS1 (by rw [sizeS1]; norm_num)
  have s2 := enumOK_enumBfs (fuel := 200) enumS2 (by rw [sizeS2]; norm_num)
  rw [sizeCa] at a
  rw [sizeNa] at b
  rw [sizeCv] at c
  rw [sizeNV] at d
  rw [sizeNE] at e
  rw [sizeS0] at s0
  rw [sizeS1] at s1
  rw [sizeS2] at s2
  unfold chkEnum45 cCa cNa cCv cNV cNE cS
  simp only [List.all_cons, List.all_nil, a.1, a.2, b.1, b.2, c.1, c.2, d.1, d.2, e.1, e.2,
    s0.1, s0.2, s1.1, s1.2, s2.1, s2.2]
  rfl

theorem wAll : ∀ k < 1080, wK WEK (CertificateChecks.KernelMisc.J2C3.CzP.F k) = true :=
  all_of_chunks 90 12 wCzS

theorem e0cAll : ∀ k < 1080, e0cK (CertificateChecks.KernelMisc.J2C3.CzP.F k) = true :=
  all_of_chunks 90 12 e0cCzS

theorem e0nAll : ∀ k < 2160,
    e0nK (memK 54 (lget NEP)) (CertificateChecks.KernelMisc.J2C3.NZP.F k) = true :=
  all_of_chunks 90 24 e0nNZS

theorem outAll : ∀ k < 72, outK (cm P0 OU) (lget NaP k) = true := all_of_chunks 72 1 outNaS

theorem sczAll : ∀ k < 64, sczK (lget S0P k) = true := all_of_chunks 64 1 sczSS

theorem sprodAll : ∀ k < 64, sprodK (lget S0P k) = true := all_of_chunks 64 1 sprodSS

theorem lawAll : ∀ a < 4, lawK a = true := all_of_chunks 1 4 lawCS

theorem phAll : ∀ j < 64, phK j = true := all_of_chunks 64 1 phCS

theorem phDAll : ∀ j < 64, phD j = true := all_of_chunks 64 1 phDCS

end CertificateChecks.KernelMisc.J2En

end
