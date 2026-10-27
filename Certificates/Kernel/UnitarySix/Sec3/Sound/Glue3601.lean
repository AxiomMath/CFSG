module

public import Certificates.Kernel.UnitarySix.Sec3.G3601
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6

theorem chA3_k' : chA3.ok = true ∧ chA3.order = 4096 :=
  ⟨chA3_K.facts'.1, chA3_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA4_k' : chA4.ok = true ∧ chA4.order = 16 :=
  ⟨chA4_K.facts'.1, chA4_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX8_k' : chX8.ok = true ∧ chX8.order = 4 :=
  ⟨chX8_K.facts'.1, chX8_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chSig_k' : chSig.ok = true ∧ chSig.order = 6 :=
  ⟨chSig_K.facts'.1, chSig_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chLam_k' : chLam.ok = true ∧ chLam.order = 60 :=
  ⟨chLam_K.facts'.1, chLam_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chZ2S_k' : chZ2S.ok = true ∧ chZ2S.order = 8 :=
  ⟨chZ2S_K.facts'.1, chZ2S_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX6Z_k' : chX6Z.ok = true ∧ chX6Z.order = 32 :=
  ⟨chX6Z_K.facts'.1, chX6Z_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chZ_k' : chZ.ok = true ∧ chZ.order = 2 :=
  ⟨chZ_K.facts'.1, chZ_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX1Z_k' : chX1Z.ok = true ∧ chX1Z.order = 32 :=
  ⟨chX1Z_K.facts'.1, chX1Z_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chP2_k' : chP2.ok = true ∧ chP2.order = 1474560 :=
  ⟨chP2_K.facts'.1, chP2_K.facts'.2.1.trans (by decide +kernel)⟩

theorem conj_O_all' {c d : ChainData} {kS nb BP NS kS' nb' BP' NS' : ℕ}
    {PS PSI LR TR TRI PS' PSI' LR' TR' TRI' : ℕ → ℕ}
    (hc : ChainK c kS nb BP NS PS PSI LR TR TRI)
    (hd : ChainK d kS' nb' BP' NS' PS' PSI' LR' TR' TRI')
    (hP : ∀ j < c.gens.length, PermK (PS j) (PSI j) = true)
    (hQ : ∀ i < d.gens.length, PermK (PS' i) (PSI' i) = true)
    (hk : ((List.range c.gens.length).all fun j => (List.range d.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR' TRI' BP' nb' 0
        (pcomp 693 10 (mask 10) (PS j) (pcomp 693 10 (mask 10) (PS' i) (PSI j)))) = true) :
    (c.O.all fun x => d.O.all fun a => siftA 693 d.levels d.B 0 (conjA 693 x a)) = true := by
  rw [hc.O_all]
  refine List.all_eq_true.2 fun j hj => ?_
  rw [hd.O_all]
  refine List.all_eq_true.2 fun i hi => ?_
  have hj' := hP j (List.mem_range.1 hj)
  have hi' := PermK.canon (hQ i (List.mem_range.1 hi))
  rw [conj_unpack hj' hi', hd.sift' (conj_canon hi' hj')]
  exact List.all_eq_true.1 (List.all_eq_true.1 hk j hj) i hi

theorem wconj_O_all' {d : ChainData} {kS' nb' BP' NS' : ℕ} {PS' PSI' LR' TR' TRI' : ℕ → ℕ}
    (hd : ChainK d kS' nb' BP' NS' PS' PSI' LR' TR' TRI')
    (hQ : ∀ i < d.gens.length, PermK (PS' i) (PSI' i) = true) {w : List ℕ}
    (hw : ∀ k ∈ w, k < 18) (hp : PermK (wK w) (wKI w) = true)
    (hk : ((List.range d.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR' TRI' BP' nb' 0
        (pcomp 693 10 (mask 10) (wK w) (pcomp 693 10 (mask 10) (PS' i) (wKI w)))) = true) :
    (d.O.all fun a => siftA 693 d.levels d.B 0 (conjA 693 (wA w) a)) = true := by
  rw [hd.O_all]
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := PermK.canon (hQ i (List.mem_range.1 hi))
  rw [wconj hi' hw hp, hd.sift' (conj_canon hi' hp)]
  exact List.all_eq_true.1 hk i hi

theorem xNorm_k' : xNormCheck = true := by
  have hk := kXN
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hk
  unfold xNormCheck lvA4 lvA3
  rw [Bool.and_eq_true, Array.all_append, Array.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨conj_O_all' chLam_K chA4_K chLam_P chA4_P h1,
    ⟨conj_O_all' chLam_K chA3_K chLam_P chA3_P h2, conj_O_all' chSig_K chA3_K chSig_P chA3_P h3⟩,
    ?_⟩
  simp only [List.all_toArray', List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨wconj_O_all' chA3_K chA3_P (w := [4, 17]) (by decide) (perm_words2 _ (by simp)) h4,
    wconj_O_all' chA3_K chA3_P (w := wj₀) (by decide) (perm_words _ (by simp)) h5⟩

end CertificateChecks.KernelU6.Sec3
