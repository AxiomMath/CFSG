module

public import Certificates.Kernel.Sporadic.OddCore.MNAll
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import Certificates.Kernel.Sporadic.OddCore.MNC0
public import Certificates.Kernel.Sporadic.OddCore.MNC1
public import Certificates.Kernel.Sporadic.OddCore.MNC2
public import Certificates.Kernel.Sporadic.OddCore.MNC3
public import Certificates.Kernel.Sporadic.OddCore.MNK1E0
public import Certificates.Kernel.Sporadic.OddCore.MNK1E1
public import Certificates.Kernel.Sporadic.OddCore.MNK1E2
public import Certificates.Kernel.Sporadic.OddCore.MNK1E3
public import Certificates.Kernel.Sporadic.OddCore.MNK1H
public import Certificates.Kernel.Sporadic.OddCore.MNR1E0
public import Certificates.Kernel.Sporadic.OddCore.MNR1E1
public import Certificates.Kernel.Sporadic.OddCore.MNR1H
public import Certificates.Kernel.Sporadic.OddCore.MNR2E0
public import Certificates.Kernel.Sporadic.OddCore.MNR2E1
public import Certificates.Kernel.Sporadic.OddCore.MNR2E2
public import Certificates.Kernel.Sporadic.OddCore.MNR2E3
public import Certificates.Kernel.Sporadic.OddCore.MNR2E4
public import Certificates.Kernel.Sporadic.OddCore.MNR2E5
public import Certificates.Kernel.Sporadic.OddCore.MNR2E6
public import Certificates.Kernel.Sporadic.OddCore.MNR2E7
public import Certificates.Kernel.Sporadic.OddCore.MNR2E8
public import Certificates.Kernel.Sporadic.OddCore.MNR2H0
public import Certificates.Kernel.Sporadic.OddCore.MNR2H1
public import Certificates.Kernel.Sporadic.OddCore.MNR2H2
public import Certificates.Kernel.Sporadic.OddCore.MNR2H3
public import Certificates.Kernel.Sporadic.OddCore.MNS0
public import Certificates.Kernel.Sporadic.OddCore.MNS1
public import Certificates.Kernel.Sporadic.OddCore.MNS2
public import Certificates.Kernel.Sporadic.OddCore.MNS3
public import Certificates.Kernel.Sporadic.OddCore.MNS4
public import Certificates.Kernel.Sporadic.OddCore.MNS5
public import Certificates.Kernel.Sporadic.OddCore.MNS6
public import Certificates.Kernel.Sporadic.OddCore.MNS7
public import Certificates.Kernel.Sporadic.OddCore.MNS8

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem base : szOK 275 9 = true ∧ canonK 275 9 (mask 9) (275 * 9) idK = true ∧
    CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 30 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (F k),
      bAnd(canonK 275 9 (mask 9) (275 * 9) (I k), invEqK 275 9 (mask 9) (275 * 9) (F k) (I k)))) =
      true ∧
    allN 2 (fun j => bAnd(canonK 275 9 (mask 9) (275 * 9) (S j),
      canonK 275 9 (mask 9) (275 * 9) (SI j))) = true := by
  simpa only [bAnd_iff] using k_base

theorem hn : szOK 275 9 = true := base.1

theorem hidc : canonK 275 9 (mask 9) (275 * 9) (pidn 275 9) = true := base.2.1

theorem hidA : idA 275 = unpack 275 9 (pidn 275 9) := (idK_sound base.2.2.1).symm

theorem hid : idT 275 = tabT (unpack 275 9 (pidn 275 9)) := by rw [idT_tabT, hidA]

theorem Fc {k : Nat} (hk : k < 30) : canonK 275 9 (mask 9) (275 * 9) (F k) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).1

theorem Ic {k : Nat} (hk : k < 30) : canonK 275 9 (mask 9) (275 * 9) (I k) = true :=
  ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).2).1

theorem Sc {j : Nat} (hj : j < 2) : canonK 275 9 (mask 9) (275 * 9) (S j) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2 j hj)).1

theorem SIc {j : Nat} (hj : j < 2) : canonK 275 9 (mask 9) (275 * 9) (SI j) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2 j hj)).2

theorem Finv {k : Nat} (hk : k < 30) : invEqK 275 9 (mask 9) (275 * 9) (F k) (I k) = true :=
  ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).2).2

theorem tabF {k : Nat} (hk : k < 30) : mclCentTbl k = tabT (unpack 275 9 (F k)) := by
  change mclCentTbl k = tabT (unpack 275 9 (McLCT.F k))
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLCT.all (by norm_num) k hk
  rw [← McLCT.eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem invF {k : Nat} (hk : k < 30) : invT 275 (mclCentTbl k) = tabT (unpack 275 9 (I k)) := by
  rw [tabF hk, invT_unpack (by norm_num) (Finv hk)]

theorem permF {k : Nat} (hk : k < 30) : permOK 275 (mclCentTbl k) = true := by
  rw [tabF hk]
  exact permOK_unpack (Fc hk) (Finv hk)

theorem invOKF {k : Nat} (hk : k < 30) : invOK 275 (mclCentTbl k) (invT 275 (mclCentTbl k)) = true
    :=
    by
  rw [invF hk, tabF hk]
  exact invOK_unpack (Fc hk) (Ic hk) (Finv hk)

theorem sift_eq {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) :
    mclSift (tabT (unpack 275 9 X)) = sK X := by
  unfold mclSift
  rw [natArr_tabT hX]
  exact CFSG.KC.J2Cover.siftK_eq CertificateChecks.KernelCensus.McLK.binds
      CertificateChecks.KernelCensus.McLK.hperm CertificateChecks.KernelCensus.McLC.hl hX

theorem involF {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) :
    involOK 275 (tabT (unpack 275 9 X)) = involK X := by
  rw [involOK_unpack' (by norm_num) hid hidc hX]
  rfl

theorem pows (X : Nat) : Pows 275 9 X (fun e => pw e X) := by
  refine ⟨rfl, fun e => ?_⟩
  change strictN (pw e X) (fun a => pc X a) = _
  rw [strictN_app']
  rfl

theorem canonP {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) (e : Nat) :
    canonK 275 9 (mask 9) (275 * 9) (pw e X) = true := pows_canon (pows X) hidc hX e

theorem compF {p q : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true)
    (hq : canonK 275 9 (mask 9) (275 * 9) q = true) :
    canonK 275 9 (mask 9) (275 * 9) (pcomp 275 9 (mask 9) p q) = true := canonK_pcomp hp hq

theorem commF {p q : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true)
    (hq : canonK 275 9 (mask 9) (275 * 9) q = true) :
    commTT 275 (tabT (unpack 275 9 p)) (tabT (unpack 275 9 q)) = commK p q := by
  rw [commTT_unpack hp hq]
  rfl

theorem ordF {X : Nat} (hX : canonK 275 9 (mask 9) (275 * 9) X = true) (m : Nat) :
    ordTest 275 m (tabT (unpack 275 9 X)) =
      (isId m X && (divParts m).all fun e => notId e X) := by
  rw [ordTest_unpack (pows X) hidA hidc hX]
  congr 1

theorem pg_tabs : TabsOK 275 9 2 S mclPGTbls := by
  refine ⟨rfl, fun j hj => ⟨?_, Sc hj⟩⟩
  have hb := CertificateChecks.KernelCensus.McLK.binds.2.2.2.2.1 j (by omega)
  interval_cases j
  · change tabT ((CFSG.Sporadic.Schreier.mclStrongArrs)[0]!) = _
    rw [hb]
    rfl
  · change tabT ((CFSG.Sporadic.Schreier.mclStrongArrs)[1]!) = _
    rw [hb]
    rfl

theorem pgi_tabs : TabsOK 275 9 2 SI mclPGInvTbls :=
  TabsOK_inv pg_tabs fun j hj => ⟨allN_spec CertificateChecks.KernelCensus.McLK.hperm j (by omega),
      SIc hj⟩

theorem tabs_range (a k : Nat) (hk : a + k ≤ 30) :
    TabsOK 275 9 k (fun j => F (Nat.add a j))
      ((List.range k).map fun j => mclCentTbl (a + j)).toArray := by
  refine ⟨by simp, fun j hj => ⟨?_, Fc (by change a + j < 30; omega)⟩⟩
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  exact tabF (by omega)

theorem invs_range (a k : Nat) (hk : a + k ≤ 30) :
    ∀ j < k, invEqK 275 9 (mask 9) (275 * 9) (F (Nat.add a j)) (I (Nat.add a j)) = true ∧
      canonK 275 9 (mask 9) (275 * 9) (I (Nat.add a j)) = true :=
  fun j hj => ⟨Finv (by change a + j < 30; omega), Ic (by change a + j < 30; omega)⟩

theorem itabs_range (a k : Nat) (hk : a + k ≤ 30) :
    TabsOK 275 9 k (fun j => I (Nat.add a j))
      (((List.range k).map fun j => mclCentTbl (a + j)).toArray.map (invT 275)) :=
  TabsOK_inv (tabs_range a k hk) (invs_range a k hk)

theorem eq_of {G G' : Nat → Nat} {k : Nat} (h : allN k (fun j => Nat.beq (G' j) (G j)) = true) :
    ∀ j < k, G' j = G j := fun j hj => Nat.eq_of_beq_eq_true (allN_spec h j hj)


theorem cover {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem blk {F : Nat → Bool} {a b : Nat} (h1 : ∀ s < a, F s = true)
    (h2 : ∀ s < b, F (a + s) = true) : ∀ s < a + b, F s = true := by
  intro s hs
  by_cases h : s < a
  · exact h1 s h
  · have e : a + (s - a) = s := by omega
    have := h2 (s - a) (by omega)
    rwa [e] at this

theorem pe_join {k cnt L N : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hL : 0 < L)
    (hc : cnt ≤ L * N) (h : ∀ s < N, peSl k cnt G GI T PL POS SRT SRI L s = true) :
    ∀ i < cnt, penumPtK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI i = true := by
  intro i hi
  refine cover (N := N) (P := fun i => i < cnt →
    penumPtK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI i = true) hL
    (fun s hs i h1 h2 => ?_) i (by omega) hi
  have h' : penumSlK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI (L * s) L = true :=
    h s hs
  exact penumSl_spec h' i h1 h2

theorem sl_join {cnt L N : Nat} {P : Nat → Bool} (hL : 0 < L) (hc : cnt ≤ L * N)
    (h : ∀ s < N, slSl cnt P L s = true) : ∀ i < cnt, P i = true := by
  intro i hi
  refine cover (N := N) (P := fun i => i < cnt → P i = true) hL (fun s hs i h1 h2 => ?_) i (by omega) hi
  have h' : slK cnt P (L * s) L = true := h s hs
  exact slK_spec h' i h1 h2

theorem hsF_join {cnt L N : Nat} {T HS HSI : Nat → Nat} (hL : 0 < L) (hc : cnt ≤ L * N)
    (h : ∀ s < N, slSl cnt (hsPF cnt T HS HSI) L s = true) :
    ∀ i < cnt, hsortPtK 275 9 (mask 9) cnt T HS HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq]
  exact sl_join hL hc h i hi

theorem heads : penumHdK MN.R1.R MN.R1.cnt 120000 MN.R1.T MN.R1.PL = true ∧
    penumHdK MN.R2.R MN.R2.cnt 120000 MN.R2.T MN.R2.PL = true ∧
    penumHdK idK MN.SY.cnt 120000 MN.SY.T MN.SY.PL = true ∧
    penumHdK idK MN.K1.cnt 120000 MN.K1.T MN.K1.PL = true ∧
    penumHdK idK MN.K2.cnt 120000 MN.K2.T MN.K2.PL = true ∧
    penumHdK MN.Q1a.R MN.Q1a.cnt 120000 MN.Q1a.T MN.Q1a.PL = true ∧
    penumHdK MN.Q1b.R MN.Q1b.cnt 120000 MN.Q1b.T MN.Q1b.PL = true ∧
    penumHdK MN.Q1c.R MN.Q1c.cnt 120000 MN.Q1c.T MN.Q1c.PL = true ∧
    penumHdK MN.Q1d.R MN.Q1d.cnt 120000 MN.Q1d.T MN.Q1d.PL = true ∧
    penumHdK MN.Q1e.R MN.Q1e.cnt 120000 MN.Q1e.T MN.Q1e.PL = true ∧
    penumHdK MN.Q2a.R MN.Q2a.cnt 120000 MN.Q2a.T MN.Q2a.PL = true ∧
    penumHdK MN.Q2b.R MN.Q2b.cnt 120000 MN.Q2b.T MN.Q2b.PL = true ∧
    penumHdK MN.Q2c.R MN.Q2c.cnt 120000 MN.Q2c.T MN.Q2c.PL = true ∧
    penumHdK MN.Q2d.R MN.Q2d.cnt 120000 MN.Q2d.T MN.Q2d.PL = true := by
  simpa only [bAnd_iff] using k_heads

theorem sizes : MN.R1.cnt = 22275 ∧ MN.R2.cnt = 113400 ∧ MN.SY.cnt = 256 ∧ MN.K1.cnt = 40320 ∧
    MN.K2.cnt = 7920 ∧ MN.Q1a.cnt = 112 ∧ MN.Q1b.cnt = 2880 ∧ MN.Q1c.cnt = 2880 ∧
    MN.Q1d.cnt = 1344 ∧ MN.Q1e.cnt = 1120 ∧ MN.Q2a.cnt = 1584 ∧ MN.Q2b.cnt = 720 ∧
    MN.Q2c.cnt = 720 ∧ MN.Q2d.cnt = 440 := by
  have h := k_sizes
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact h

theorem r1_pe : ∀ i < MN.R1.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.R1.G MN.R1.GI 2
    MN.R1.cnt MN.R1.T MN.R1.PL MN.R1.POS MN.R1.SRT MN.R1.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.1]) (blk R1E0.all R1E1.all)

theorem r1_hs : ∀ i < MN.R1.cnt, hsortPtK 275 9 (mask 9) MN.R1.cnt MN.R1.T MN.R1.HS MN.R1.HSI i =
    true :=
  hsF_join (by norm_num) (by norm_num [sizes.1]) R1HF.all

theorem r2_pe : ∀ i < MN.R2.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.R2.G MN.R2.GI 2
    MN.R2.cnt MN.R2.T MN.R2.PL MN.R2.POS MN.R2.SRT MN.R2.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.1])
    (blk (blk (blk (blk (blk (blk (blk (blk R2E0.all R2E1.all) R2E2.all) R2E3.all) R2E4.all)
      R2E5.all) R2E6.all) R2E7.all) R2E8.all)

theorem r2_hs : ∀ i < MN.R2.cnt, hsortPtK 275 9 (mask 9) MN.R2.cnt MN.R2.T MN.R2.HS MN.R2.HSI i =
    true :=
  hsF_join (by norm_num) (by norm_num [sizes.2.1])
    (blk (blk (blk R2HF0.all R2HF1.all) R2HF2.all) R2HF3.all)

theorem k1_pe : ∀ i < MN.K1.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.K1.G MN.K1.GI 2
    MN.K1.cnt MN.K1.T MN.K1.PL MN.K1.POS MN.K1.SRT MN.K1.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.1]) (blk (blk (blk K1E0.all K1E1.all) K1E2.all) K1E3.all)

theorem k1_hs : ∀ i < MN.K1.cnt, hsortPtK 275 9 (mask 9) MN.K1.cnt MN.K1.T MN.K1.HS MN.K1.HSI i =
    true :=
  hsF_join (by norm_num) (by norm_num [sizes.2.2.2.1]) K1HF.all

theorem k2_pe : ∀ i < MN.K2.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.K2.G MN.K2.GI 4
    MN.K2.cnt MN.K2.T MN.K2.PL MN.K2.POS MN.K2.SRT MN.K2.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.1]) (blk K2E0.all K2E1.all)

theorem k2_hs : ∀ i < MN.K2.cnt, hsortPtK 275 9 (mask 9) MN.K2.cnt MN.K2.T MN.K2.HS MN.K2.HSI i =
    true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.1]) K2H.all

theorem sy_pe : ∀ i < MN.SY.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.SY.G MN.SY.GI 3
    MN.SY.cnt MN.SY.T MN.SY.PL MN.SY.POS MN.SY.SRT MN.SY.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.1]) SYE.all

theorem sy_hs : ∀ i < MN.SY.cnt, hsortPtK 275 9 (mask 9) MN.SY.cnt MN.SY.T MN.SY.HS MN.SY.HSI i =
    true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.1]) SYH.all

theorem q1a_pe : ∀ i < MN.Q1a.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q1a.G MN.Q1a.GI 2
    MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL MN.Q1a.POS MN.Q1a.SRT MN.Q1a.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.1]) Q1aE.all

theorem q1a_hs : ∀ i < MN.Q1a.cnt, hsortPtK 275 9 (mask 9) MN.Q1a.cnt MN.Q1a.T MN.Q1a.HS
    MN.Q1a.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.1]) Q1aH.all

theorem q1b_pe : ∀ i < MN.Q1b.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q1b.G MN.Q1b.GI 2
    MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL MN.Q1b.POS MN.Q1b.SRT MN.Q1b.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.1]) Q1bE.all

theorem q1b_hs : ∀ i < MN.Q1b.cnt, hsortPtK 275 9 (mask 9) MN.Q1b.cnt MN.Q1b.T MN.Q1b.HS
    MN.Q1b.HSI i = true :=
  hsF_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.1]) Q1bHF.all

theorem q1c_pe : ∀ i < MN.Q1c.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q1c.G MN.Q1c.GI 2
    MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL MN.Q1c.POS MN.Q1c.SRT MN.Q1c.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.1]) Q1cE.all

theorem q1c_hs : ∀ i < MN.Q1c.cnt, hsortPtK 275 9 (mask 9) MN.Q1c.cnt MN.Q1c.T MN.Q1c.HS
    MN.Q1c.HSI i = true :=
  hsF_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.1]) Q1cHF.all

theorem q1d_pe : ∀ i < MN.Q1d.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q1d.G MN.Q1d.GI 2
    MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL MN.Q1d.POS MN.Q1d.SRT MN.Q1d.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.1]) Q1dE.all

theorem q1d_hs : ∀ i < MN.Q1d.cnt, hsortPtK 275 9 (mask 9) MN.Q1d.cnt MN.Q1d.T MN.Q1d.HS
    MN.Q1d.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.1]) Q1dH.all

theorem q1e_pe : ∀ i < MN.Q1e.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q1e.G MN.Q1e.GI 2
    MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL MN.Q1e.POS MN.Q1e.SRT MN.Q1e.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.1]) Q1eE.all

theorem q1e_hs : ∀ i < MN.Q1e.cnt, hsortPtK 275 9 (mask 9) MN.Q1e.cnt MN.Q1e.T MN.Q1e.HS
    MN.Q1e.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.1]) Q1eH.all

theorem q2a_pe : ∀ i < MN.Q2a.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q2a.G MN.Q2a.GI 4
    MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL MN.Q2a.POS MN.Q2a.SRT MN.Q2a.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.1]) Q2aE.all

theorem q2a_hs : ∀ i < MN.Q2a.cnt, hsortPtK 275 9 (mask 9) MN.Q2a.cnt MN.Q2a.T MN.Q2a.HS
    MN.Q2a.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.1]) Q2aH.all

theorem q2b_pe : ∀ i < MN.Q2b.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q2b.G MN.Q2b.GI 4
    MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL MN.Q2b.POS MN.Q2b.SRT MN.Q2b.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.1]) Q2bE.all

theorem q2b_hs : ∀ i < MN.Q2b.cnt, hsortPtK 275 9 (mask 9) MN.Q2b.cnt MN.Q2b.T MN.Q2b.HS
    MN.Q2b.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.1]) Q2bH.all

theorem q2c_pe : ∀ i < MN.Q2c.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q2c.G MN.Q2c.GI 4
    MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL MN.Q2c.POS MN.Q2c.SRT MN.Q2c.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.2.1]) Q2cE.all

theorem q2c_hs : ∀ i < MN.Q2c.cnt, hsortPtK 275 9 (mask 9) MN.Q2c.cnt MN.Q2c.T MN.Q2c.HS
    MN.Q2c.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.2.1]) Q2cH.all

theorem q2d_pe : ∀ i < MN.Q2d.cnt, penumPtK 275 9 (mask 9) (275 * 9) true MN.Q2d.G MN.Q2d.GI 4
    MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL MN.Q2d.POS MN.Q2d.SRT MN.Q2d.SRI i = true :=
  pe_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.2.2]) Q2dE.all

theorem q2d_hs : ∀ i < MN.Q2d.cnt, hsortPtK 275 9 (mask 9) MN.Q2d.cnt MN.Q2d.T MN.Q2d.HS
    MN.Q2d.HSI i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.2.2.2.2.2.2.2.2.2]) Q2dH.all

theorem sel1_all : ∀ i < MN.K1.cnt, sel1K i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.1]) (blk (blk (blk C0.all C1.all) C2.all) C3.all)

theorem sel2_all : ∀ i < MN.K2.cnt, sel2K i = true :=
  sl_join (by norm_num) (by norm_num [sizes.2.2.2.2.1]) (blk Sel2a.all Sel2b.all)


@[expose] def cgL (a k : Nat) : List Table := (List.range k).map fun j => mclCentTbl (a + j)

theorem cg_tabs (a k : Nat) (hk : a + k ≤ 30) :
    TabsOK 275 9 k (fun j => F (Nat.add a j)) (cgL a k).toArray :=
  tabs_range a k hk

theorem cgi_tabs (a k : Nat) (hk : a + k ≤ 30) :
    TabsOK 275 9 k (fun j => I (Nat.add a j)) ((cgL a k).toArray.map (invT 275)) :=
  itabs_range a k hk

theorem sy_eq : mclSylowGenTbls = cgL 1 3 := by
  unfold mclSylowGenTbls cgL
  apply List.map_congr_left
  intro i _
  rw [Nat.add_comm]

theorem pair_of {k : Nat} {G GI S' SI' : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (G j) (S' j), Nat.beq (GI j) (SI' j))) = true) :
    (∀ j < k, G j = S' j) ∧ ∀ j < k, GI j = SI' j :=
  ⟨fun j hj => Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).1,
    fun j hj => Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).2⟩

theorem bindR : allN 2 (fun j => bAnd(Nat.beq (MN.R1.G j) (S j), Nat.beq (MN.R1.GI j) (SI j))) =
      true ∧
    allN 2 (fun j => bAnd(Nat.beq (MN.R2.G j) (S j), Nat.beq (MN.R2.GI j) (SI j))) = true ∧
    Nat.beq MN.R1.R (F 4) = true ∧ Nat.beq MN.R2.R (F 17) = true := by
  simpa only [bAnd_iff] using k_bindR

theorem bindM : allN 3 (fun j => bAnd(Nat.beq (MN.SY.G j) idK, Nat.beq (MN.SY.GI j) (F (Nat.succ
    j)))) =
      true ∧
    allN 2 (fun j => bAnd(Nat.beq (MN.K1.G j) idK, Nat.beq (MN.K1.GI j) (F (Nat.add 5 j)))) = true ∧
    allN 4 (fun j => bAnd(Nat.beq (MN.K2.G j) idK, Nat.beq (MN.K2.GI j) (F (Nat.add 18 j)))) = true
        := by
  simpa only [bAnd_iff] using k_bindM

theorem bindQ : qbK 5 2 7 MN.Q1a.G MN.Q1a.GI MN.Q1a.R = true ∧ qbK 5 2 9 MN.Q1b.G MN.Q1b.GI
    MN.Q1b.R = true ∧
    qbK 5 2 11 MN.Q1c.G MN.Q1c.GI MN.Q1c.R = true ∧ qbK 5 2 13 MN.Q1d.G MN.Q1d.GI MN.Q1d.R = true ∧
    qbK 5 2 15 MN.Q1e.G MN.Q1e.GI MN.Q1e.R = true ∧ qbK 18 4 22 MN.Q2a.G MN.Q2a.GI MN.Q2a.R = true ∧
    qbK 18 4 24 MN.Q2b.G MN.Q2b.GI MN.Q2b.R = true ∧ qbK 18 4 26 MN.Q2c.G MN.Q2c.GI MN.Q2c.R = true
        ∧
    qbK 18 4 28 MN.Q2d.G MN.Q2d.GI MN.Q2d.R = true := by
  simpa only [bAnd_iff] using k_bindQ

theorem qb_of {a k r R : Nat} {G GI : Nat → Nat} (h : qbK a k r G GI R = true) :
    (∀ j < k, G j = F (Nat.add a j)) ∧ (∀ j < k, GI j = I (Nat.add a j)) ∧ R = F r := by
  unfold qbK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨(pair_of h1).1, (pair_of h1).2, Nat.eq_of_beq_eq_true h2⟩

theorem recR1 : conjClosureH 275 mclPGTbls mclPGInvTbls (mclCentTbl 4) 120000 =
      hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL ∧
    conjTreeOK 275 mclPGTbls mclPGInvTbls (mclCentTbl 4) (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).1
      (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).2.1 (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).2.2 =
          true ∧
    hkeysDistinct 275 (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).1.toList = true :=
  conjH_sound hn (TabsOK_congr (pair_of bindR.1).1 pg_tabs) (TabsOK_congr (pair_of bindR.1).2
      pgi_tabs)
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindR.2.2.1]) heads.1 r1_pe r1_hs

theorem recR2 : conjClosureH 275 mclPGTbls mclPGInvTbls (mclCentTbl 17) 120000 =
      hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL ∧
    conjTreeOK 275 mclPGTbls mclPGInvTbls (mclCentTbl 17) (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).1
      (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).2.1 (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).2.2 =
          true ∧
    hkeysDistinct 275 (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).1.toList = true :=
  conjH_sound hn (TabsOK_congr (pair_of bindR.2.1).1 pg_tabs)
    (TabsOK_congr (pair_of bindR.2.1).2 pgi_tabs)
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindR.2.2.2]) heads.2.1 r2_pe r2_hs

theorem recSY : mulClosureH 275 (cgL 1 3).toArray 120000 = hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL ∧
    mulTreeOK 275 (cgL 1 3).toArray (hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL).1
      (hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL).2.1 (hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL).2.2 =
          true ∧
    hkeysDistinct 275 (hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of bindM.1
  have hGI' : ∀ j < 3, MN.SY.GI j = F (Nat.add 1 j) := fun j hj => by
    rw [hGI j hj]
    change F (j + 1) = F (1 + j)
    rw [Nat.add_comm]
  exact mulH_sound hn hG (TabsOK_congr hGI' (cg_tabs 1 3 (by norm_num))) heads.2.2.1 sy_pe sy_hs

theorem recK1 : mulClosureH 275 (cgL 5 2).toArray 120000 = hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL ∧
    mulTreeOK 275 (cgL 5 2).toArray (hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).1
      (hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).2.1 (hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).2.2 =
          true ∧
    hkeysDistinct 275 (hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of bindM.2.1
  exact mulH_sound hn hG (TabsOK_congr hGI (cg_tabs 5 2 (by norm_num))) heads.2.2.2.1 k1_pe k1_hs

theorem recK2 : mulClosureH 275 (cgL 18 4).toArray 120000 = hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL ∧
    mulTreeOK 275 (cgL 18 4).toArray (hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).1
      (hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).2.1 (hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).2.2 =
          true ∧
    hkeysDistinct 275 (hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of bindM.2.2
  exact mulH_sound hn hG (TabsOK_congr hGI (cg_tabs 18 4 (by norm_num))) heads.2.2.2.2.1 k2_pe
    k2_hs


theorem recQ1a : conjClosureH 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275))
      (mclCentTbl 7) 120000 = hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL ∧
    conjTreeOK 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275)) (mclCentTbl 7)
      (hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL).1 (hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL).2.1
      (hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 5 2 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 5 2 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.1
    q1a_pe q1a_hs

theorem recQ1b : conjClosureH 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275))
      (mclCentTbl 9) 120000 = hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL ∧
    conjTreeOK 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275)) (mclCentTbl 9)
      (hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL).1 (hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL).2.1
      (hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 5 2 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 5 2 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.1
    q1b_pe q1b_hs

theorem recQ1c : conjClosureH 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275))
      (mclCentTbl 11) 120000 = hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL ∧
    conjTreeOK 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275)) (mclCentTbl 11)
      (hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL).1 (hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL).2.1
      (hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 5 2 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 5 2 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.1
    q1c_pe q1c_hs

theorem recQ1d : conjClosureH 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275))
      (mclCentTbl 13) 120000 = hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL ∧
    conjTreeOK 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275)) (mclCentTbl 13)
      (hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL).1 (hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL).2.1
      (hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 5 2 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 5 2 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.1
    q1d_pe q1d_hs

theorem recQ1e : conjClosureH 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275))
      (mclCentTbl 15) 120000 = hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL ∧
    conjTreeOK 275 (cgL 5 2).toArray ((cgL 5 2).toArray.map (invT 275)) (mclCentTbl 15)
      (hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL).1 (hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL).2.1
      (hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 5 2 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 5 2 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.2.1
    q1e_pe q1e_hs

theorem recQ2a : conjClosureH 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275))
      (mclCentTbl 22) 120000 = hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL ∧
    conjTreeOK 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275)) (mclCentTbl 22)
      (hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL).1 (hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL).2.1
      (hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 18 4 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 18 4 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.2.2.1
    q2a_pe q2a_hs

theorem recQ2b : conjClosureH 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275))
      (mclCentTbl 24) 120000 = hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL ∧
    conjTreeOK 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275)) (mclCentTbl 24)
      (hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL).1 (hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL).2.1
      (hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.2.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 18 4 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 18 4 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.2.2.2.1
    q2b_pe q2b_hs

theorem recQ2c : conjClosureH 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275))
      (mclCentTbl 26) 120000 = hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL ∧
    conjTreeOK 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275)) (mclCentTbl 26)
      (hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL).1 (hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL).2.1
      (hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.2.2.2.2.1
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 18 4 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 18 4 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.2.2.2.2.1
    q2c_pe q2c_hs

theorem recQ2d : conjClosureH 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275))
      (mclCentTbl 28) 120000 = hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL ∧
    conjTreeOK 275 (cgL 18 4).toArray ((cgL 18 4).toArray.map (invT 275)) (mclCentTbl 28)
      (hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL).1 (hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL).2.1
      (hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL).1.toList = true := by
  obtain ⟨h1, h2, h3⟩ := qb_of bindQ.2.2.2.2.2.2.2.2
  exact conjH_sound hn (TabsOK_congr h1 (cg_tabs 18 4 (by norm_num)))
    (TabsOK_congr h2 (cgi_tabs 18 4 (by norm_num))) (by rw [tabF (by norm_num), h3])
        heads.2.2.2.2.2.2.2.2.2.2.2.2.2
    q2d_pe q2d_hs

theorem u_tab : mclOuterTbl = tabT (unpack 275 9 (F 0)) := tabF (by norm_num)

theorem ufacts : involK (F 0) = true ∧ bIf(sK (F 0), false, true) = true ∧
    allN 2 (fun j => bAnd(sK (S j), sK (pc (pc (F 0) (S j)) (I 0)))) = true := by
  simpa only [bAnd_iff] using k_u

theorem notB {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem orB {a b : Bool} (h : bIf(a, true, b) = true) : (a || b) = true := by
  cases a
  · simpa using h
  · rfl

theorem succ_eq (a j : Nat) : Nat.add a j = a + j := rfl

theorem sy_tabs' : TabsOK 275 9 3 (fun j => F (Nat.succ j)) (cgL 1 3).toArray :=
  TabsOK_congr (fun j _ => by
    change F (j + 1) = F (1 + j)
    rw [Nat.add_comm]) (cg_tabs 1 3 (by norm_num))

theorem sy_invs : ∀ j < 3, invEqK 275 9 (mask 9) (275 * 9) (F (Nat.succ j)) (I (Nat.succ j)) = true
    ∧
    canonK 275 9 (mask 9) (275 * 9) (I (Nat.succ j)) = true :=
  fun j hj => ⟨Finv (by omega), Ic (by omega)⟩

theorem sy_cl : ∀ c < MN.SY.cnt * (3 + 3), findPtK MN.SY.cnt MN.SY.T
    (prodQK 275 9 (mask 9) (3 + 3) MN.SY.T (bothK 3 (fun j => F (Nat.succ j))
      (fun j => I (Nat.succ j)))) MN.SYCl c = true :=
  fun c hc => slK_spec syCl c (Nat.zero_le _) (by change c < 0 + MN.SY.cnt * 6; omega) hc

theorem syl_ok : CFSG.Sporadic.SmallOddCore.sylowOK 275 120000 mclPGTbls mclPGInvTbls mclSift
    mclOuterTbl
    mclSylowGenTbls
    mclSylowOrder = true := by
  unfold CFSG.Sporadic.SmallOddCore.sylowOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [sy_eq, recSY.1]
  obtain ⟨hu1, hu2, hu3⟩ := ufacts
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, recSY.2.1⟩, ?_⟩, recSY.2.2⟩, ?_⟩
  · exact permF (by norm_num)
  · rw [u_tab, involF (Fc (by norm_num))]
    exact hu1
  · rw [u_tab, sift_eq (Fc (by norm_num)), notB (b := sK (F 0)) hu2]
    rfl
  · exact invOKF (by norm_num)
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 2 := by rw [← pg_tabs.1]; exact hj
    rw [← getElem!_pos mclPGTbls j hj, (pg_tabs.2 j hj').1, sift_eq (Sc hj')]
    exact ((bAnd_iff _ _).1 (allN_spec hu3 j hj')).1
  · simp [mclPGInvTbls]
  · rw [CFSG.KS.TW.allIn_iff]
    intro l hl
    have hl' : l < 2 := by rw [← pg_tabs.1]; exact hl
    rw [(pg_tabs.2 l hl').1, (pgi_tabs.2 l hl').1]
    exact invOK_unpack (Sc hl') (SIc hl') (allN_spec CertificateChecks.KernelCensus.McLK.hperm l
        (by omega))
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 2 := by rw [← pg_tabs.1]; exact hj
    rw [← getElem!_pos mclPGTbls j hj, (pg_tabs.2 j hj').1, u_tab,
      invT_unpack (by norm_num) (Finv (by norm_num)),
      conjT_unpack (Fc (by norm_num)) (Ic (by norm_num)) (Sc hj'),
      sift_eq (compF (compF (Fc (by norm_num)) (Sc hj')) (Ic (by norm_num)))]
    exact ((bAnd_iff _ _).1 (allN_spec hu3 j hj')).2
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 3 := by rw [← sy_tabs'.1]; exact hj
    obtain ⟨hg, hc⟩ := sy_tabs'.2 j hj'
    dsimp only at hg hc
    rw [← getElem!_pos _ j hj, hg, invT_unpack (by norm_num) (sy_invs j hj').1, u_tab]
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack hc (sy_invs j hj').1, invOK_unpack hc (sy_invs j hj').2 (sy_invs j
        hj').1⟩,
      ?_⟩
    rw [compT_unpack hc (Fc (by norm_num)), sift_eq hc, sift_eq (compF hc (Fc (by norm_num)))]
    exact orB (allN_spec k_syl j hj')
  · exact closedOK_of (fun i hi => penumPt_canon (sy_pe i hi))
      (TabsOK_both sy_tabs' sy_invs) sy_cl
  · rw [hRec_size, sizes.2.2.1]
    rfl




theorem kodd : oddK 7 3 4 = true ∧ oddK 9 7 4 = true ∧ oddK 11 7 4 = true ∧ oddK 13 5 4 = true ∧
    oddK 15 3 4 = true ∧ oddK 22 5 17 = true ∧ oddK 24 11 17 = true ∧ oddK 26 11 17 = true ∧
    oddK 28 3 17 = true := by
  simpa only [bAnd_iff] using k_odd

theorem kconj : conjK 7 8 4 4 = true ∧ conjK 9 10 4 6 = true ∧ conjK 11 12 4 14 = true ∧
    conjK 13 14 4 14 = true ∧ conjK 15 16 4 10 = true ∧ conjK 22 23 17 4 = true ∧
    conjK 24 25 17 8 = true ∧ conjK 26 27 17 8 = true ∧ conjK 28 29 17 2 = true := by
  have h := k_conj
  simp only [bAnd_iff] at h
  exact h

theorem kreps : involK (F 4) = true ∧ involK (F 17) = true ∧ sK (F 4) = true ∧
    bIf(sK (F 17), false, true) = true ∧ sK (pc (F 17) (F 0)) = true := by
  simpa only [bAnd_iff] using k_reps

theorem kcg : allN 2 (fun j => bAnd(sK (F (Nat.add 5 j)), commK (F (Nat.add 5 j)) (F 4))) = true ∧
    allN 4 (fun j => bAnd(sK (F (Nat.add 18 j)), commK (F (Nat.add 18 j)) (F 17))) = true := by
  simpa only [bAnd_iff] using k_cg

theorem siftF {k : Nat} (hk : k < 30) : mclSift (mclCentTbl k) = sK (F k) := by
  rw [tabF hk, sift_eq (Fc hk)]

theorem commFF {a b : Nat} (ha : a < 30) (hb : b < 30) :
    commTT 275 (mclCentTbl a) (mclCentTbl b) = commK (F a) (F b) := by
  rw [tabF ha, tabF hb, commF (Fc ha) (Fc hb)]

theorem cg_all (a k t : Nat) (hk : a + k ≤ 30) (ht : t < 30)
    (h : allN k (fun j => bAnd(sK (F (Nat.add a j)), commK (F (Nat.add a j)) (F t))) = true) :
    (cgL a k).toArray.all (fun c => permOK 275 c && mclSift c && commTT 275 c (mclCentTbl t) &&
      invOK 275 c (invT 275 c)) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < k := by rw [← (cg_tabs a k hk).1]; exact hj
  have hl : Nat.add a j < 30 := by change a + j < 30; omega
  obtain ⟨hg, hc⟩ := (cg_tabs a k hk).2 j hj'
  dsimp only at hg hc
  rw [← getElem!_pos _ j hj, hg, invT_unpack (by norm_num) (Finv hl), tabF ht, sift_eq hc,
    commF hc (Fc ht)]
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec h j hj')
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨permOK_unpack hc (Finv hl), h1⟩, h2⟩, invOK_unpack hc (Ic hl) (Finv hl)⟩

theorem oddF {r p t : Nat} (hr : r < 30) (ht : t < 30) (h : oddK r p t = true)
    (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1]) :
    permOK 275 (mclCentTbl r) = true ∧ mclSift (mclCentTbl r) = true ∧
      commTT 275 (mclCentTbl r) (mclCentTbl t) = true ∧
      CFSG.Sporadic.Schreier.Native.ordTest 275 p (mclCentTbl r) = true := by
  unfold oddK at h
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using h :
    sK (F r) = true ∧ commK (F r) (F t) = true ∧ isId p (F r) = true ∧ notId 1 (F r) = true)
  refine ⟨permF hr, by rw [siftF hr]; exact h1, by rw [commFF hr ht]; exact h2, ?_⟩
  rw [tabF hr, ordF (Fc hr), hdp]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h3, h4⟩

theorem odd_conj {r p h t ord cs : Nat} (hr : r < 30) (hh : h < 30) (ht : t < 30)
    (ho : oddK r p t = true) (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1])
    (hc : conjK r h t ord = true)
    (h2 : ord % 2 = 0) (h0 : 0 < ord) {cg cgInv : Array Table} :
    oddRowOK 275 120000 mclSift (mclCentTbl t) cg cgInv
      { rep := mclCentTbl r, prime := p, classSize := cs, wit := .conj (mclCentTbl h) ord } =
        true := by
  obtain ⟨a1, a2, a3, a4⟩ := oddF hr ht ho hdp
  unfold conjK at hc
  obtain ⟨c1, hc'⟩ := (bAnd_iff _ _).1 hc
  obtain ⟨c2, hord⟩ := (bAnd_iff _ _).1 hc'
  have b7 : CFSG.Sporadic.Schreier.Native.ordTest 275 ord (compT 275 (mclCentTbl r)
      (conjT 275 (mclCentTbl h) (invT 275 (mclCentTbl h)) (mclCentTbl r))) = true := by
    rw [invF hh, tabF hh, tabF hr, conjT_unpack (Fc hh) (Ic hh) (Fc hr),
      compT_unpack (Fc hr) (compF (compF (Fc hh) (Fc hr)) (Ic hh)),
      ordF (compF (Fc hr) (compF (compF (Fc hh) (Fc hr)) (Ic hh)))]
    exact hord
  unfold oddRowOK
  simp only [a1, a2, a3, a4, permF hh, siftF hh, c1, commFF hh ht, c2, invOKF hh, b7, h2, h0,
    Bool.and_true, beq_self_eq_true, decide_true]


theorem mem_at {cnt i y : Nat} {T PL POS : Nat → Nat}
    (hT : ∀ q < cnt, canonK 275 9 (mask 9) (275 * 9) (T q) = true)
    (hy : canonK 275 9 (mask 9) (275 * 9) y = true) (h : atK cnt T POS i y = true) :
    memT 275 (hRec 275 9 cnt T PL).1 (tabT (unpack 275 9 y)) = true := by
  unfold atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hq : r32 POS i < cnt := Nat.le_of_ble_eq_true h1
  refine memT_of hq ?_
  rw [tblEq_unpack hy (hT _ hq), ← Nat.eq_of_beq_eq_true h2, Nat.beq_refl]

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < (hRec 275 9 cnt T PL).1.size) :
    (hRec 275 9 cnt T PL).1[i] = tabT (unpack 275 9 (T i)) := by
  simp [hRec]

theorem rec_lt {cnt i : Nat} {T PL : Nat → Nat} (hi : i < (hRec 275 9 cnt T PL).1.size) :
    i < cnt := by
  simpa [hRec] using hi

theorem bIf_or' {a b : Bool} (h : bIf(a, true, b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem invol_of {k : Nat} (hk : k < 30) (h : involK (F k) = true) : involOK 275 (mclCentTbl k) =
    true := by
  rw [tabF hk, involF (Fc hk)]
  exact h


theorem canonR {cnt k : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : ∀ i < cnt, penumPtK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, canonK 275 9 (mask 9) (275 * 9) (T i) = true :=
  fun i hi => penumPt_canon (h i hi)



theorem pwS (e Y : Nat) : pw (e + 1) Y = pc Y (pw e Y) := (pows Y).2 e

theorem pw1 {Y : Nat} (hY : canonK 275 9 (mask 9) (275 * 9) Y = true) : pw 1 Y = Y := by
  rw [pwS]
  exact (CFSG.KC.J2Cover.pcomp_id hY).1

theorem sel357_eq {Y : Nat} (hY : canonK 275 9 (mask 9) (275 * 9) Y = true) :
    sel357 Y = (!Nat.beq Y (pidn 275 9) && [3, 5, 7].any fun p => Nat.beq (pw p Y) (pidn 275 9)) :=
        by
  have h3 : pw 3 Y = pc Y (pc Y Y) := by rw [pwS, pwS, pw1 hY]
  have h5 : pw 5 Y = pc Y (pc Y (pc Y (pc Y Y))) := by rw [pwS, pwS, h3]
  have h7 : pw 7 Y = pc Y (pc Y (pc Y (pc Y (pc Y (pc Y Y))))) := by rw [pwS, pwS, h5]
  unfold sel357
  simp only [strictB_eq'', List.any_cons, List.any_nil, Bool.or_false, h3, h5, h7]
  unfold idK
  cases Nat.beq Y (pidn 275 9) <;> cases Nat.beq (pc Y (pc Y Y)) (pidn 275 9) <;>
    cases Nat.beq (pc Y (pc Y (pc Y (pc Y Y)))) (pidn 275 9) <;> rfl

theorem sel3511_eq {Y : Nat} (hY : canonK 275 9 (mask 9) (275 * 9) Y = true) :
    sel3511 Y = (!Nat.beq Y (pidn 275 9) && [3, 5, 11].any fun p => Nat.beq (pw p Y) (pidn 275 9))
        := by
  have h3 : pw 3 Y = pc Y (pc Y Y) := by rw [pwS, pwS, pw1 hY]
  have h5 : pw 5 Y = pc Y (pc Y (pc Y (pc Y Y))) := by rw [pwS, pwS, h3]
  have h11 : pw 11 Y = pc Y (pc Y (pc Y (pc Y (pc Y (pc Y (pc Y (pc Y (pc Y (pc Y Y))))))))) := by
    rw [pwS, pwS, pwS, pwS, pwS, pwS, h5]
  unfold sel3511
  simp only [strictB_eq'', List.any_cons, List.any_nil, Bool.or_false, h3, h5, h11]
  unfold idK
  cases Nat.beq Y (pidn 275 9) <;> cases Nat.beq (pc Y (pc Y Y)) (pidn 275 9) <;>
    cases Nat.beq (pc Y (pc Y (pc Y (pc Y Y)))) (pidn 275 9) <;> rfl

theorem selF3 {Y : Nat} (hY : canonK 275 9 (mask 9) (275 * 9) Y = true) (ps : List Nat) :
    selOK 275 ps (tabT (unpack 275 9 Y)) =
      (!Nat.beq Y (pidn 275 9) && ps.any fun p => Nat.beq (pw p Y) (pidn 275 9)) :=
  selOK_unpack (pows Y) hid hidc hY ps

theorem sel1 : (hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).1.all (fun y => !selOK 275 [3, 5, 7] y ||
    (memT 275 (hRec 275 9 MN.Q1a.cnt MN.Q1a.T MN.Q1a.PL).1 y ||
      (memT 275 (hRec 275 9 MN.Q1b.cnt MN.Q1b.T MN.Q1b.PL).1 y ||
        (memT 275 (hRec 275 9 MN.Q1c.cnt MN.Q1c.T MN.Q1c.PL).1 y ||
          (memT 275 (hRec 275 9 MN.Q1d.cnt MN.Q1d.T MN.Q1d.PL).1 y ||
            memT 275 (hRec 275 9 MN.Q1e.cnt MN.Q1e.T MN.Q1e.PL).1 y))))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR k1_pe i hi'
  rw [rec_get hi, selF3 hc, ← sel357_eq hc]
  have h := sel1_all i hi'
  unfold sel1K at h
  rw [strictB_eq''] at h
  cases hs : sel357 (MN.K1.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR q1a_pe) hc h1)
    rcases bIf_or' h1 with h2 | h2
    · exact Or.inr (Or.inl (mem_at (canonR q1b_pe) hc h2))
    rcases bIf_or' h2 with h3 | h3
    · exact Or.inr (Or.inr (Or.inl (mem_at (canonR q1c_pe) hc h3)))
    rcases bIf_or' h3 with h4 | h4
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_at (canonR q1d_pe) hc h4))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_at (canonR q1e_pe) hc h4))))

theorem sel2 : (hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).1.all (fun y => !selOK 275 [3, 5, 11] y ||
    (memT 275 (hRec 275 9 MN.Q2a.cnt MN.Q2a.T MN.Q2a.PL).1 y ||
      (memT 275 (hRec 275 9 MN.Q2b.cnt MN.Q2b.T MN.Q2b.PL).1 y ||
        (memT 275 (hRec 275 9 MN.Q2c.cnt MN.Q2c.T MN.Q2c.PL).1 y ||
          memT 275 (hRec 275 9 MN.Q2d.cnt MN.Q2d.T MN.Q2d.PL).1 y)))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR k2_pe i hi'
  rw [rec_get hi, selF3 hc, ← sel3511_eq hc]
  have h := sel2_all i hi'
  unfold sel2K at h
  rw [strictB_eq''] at h
  cases hs : sel3511 (MN.K2.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR q2a_pe) hc h1)
    rcases bIf_or' h1 with h2 | h2
    · exact Or.inr (Or.inl (mem_at (canonR q2b_pe) hc h2))
    rcases bIf_or' h2 with h3 | h3
    · exact Or.inr (Or.inr (Or.inl (mem_at (canonR q2c_pe) hc h3)))
    · exact Or.inr (Or.inr (Or.inr (mem_at (canonR q2d_pe) hc h3)))


theorem s1a : ((hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).1.size == 22275) = true := by
  rw [hRec_size, sizes.1]
  rfl

theorem s1b : ((hRec 275 9 MN.K1.cnt MN.K1.T MN.K1.PL).1.size == 40320) = true := by
  rw [hRec_size, sizes.2.2.2.1]
  rfl

theorem s2a : ((hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).1.size == 113400) = true := by
  rw [hRec_size, sizes.2.1]
  rfl

theorem s2b : ((hRec 275 9 MN.K2.cnt MN.K2.T MN.K2.PL).1.size == 7920) = true := by
  rw [hRec_size, sizes.2.2.2.2.1]
  rfl

theorem row1 : CFSG.Sporadic.SmallOddCore.classOK 275 898128000 120000 mclPGTbls mclPGInvTbls
    mclSift mclOuterTbl
    { rep := mclCentTbl 4, outer := false, classSize := 22275,
      centOrder := 40320, centGens := [mclCentTbl 5, mclCentTbl 6],
      oddPrimes := [3, 5, 7], odd := [
        { rep := mclCentTbl 7, prime := 3, classSize := 112, wit := .conj (mclCentTbl 8) 4 },
        { rep := mclCentTbl 9, prime := 7, classSize := 2880, wit := .conj (mclCentTbl 10) 6 },
        { rep := mclCentTbl 11, prime := 7, classSize := 2880, wit := .conj (mclCentTbl 12) 14 },
        { rep := mclCentTbl 13, prime := 5, classSize := 1344, wit := .conj (mclCentTbl 14) 14 },
        { rep := mclCentTbl 15, prime := 3, classSize := 1120, wit := .conj (mclCentTbl 16) 10 }] }
    (conjClosureH 275 mclPGTbls mclPGInvTbls (mclCentTbl 4) 120000) = true := by
  have e : [mclCentTbl 5, mclCentTbl 6] = cgL 5 2 := rfl
  have o1 := odd_conj (r := 7) (p := 3) (h := 8) (t := 4) (ord := 4) (cs := 112)
    (cg := (cgL 5 2).toArray) (cgInv := (cgL 5 2).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.1 (by decide) kconj.1 (by norm_num) (by norm_num)
  have o2 := odd_conj (r := 9) (p := 7) (h := 10) (t := 4) (ord := 6) (cs := 2880)
    (cg := (cgL 5 2).toArray) (cgInv := (cgL 5 2).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.1 (by decide) kconj.2.1 (by norm_num) (by norm_num)
  have o3 := odd_conj (r := 11) (p := 7) (h := 12) (t := 4) (ord := 14) (cs := 2880)
    (cg := (cgL 5 2).toArray) (cgInv := (cgL 5 2).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.1 (by decide) kconj.2.2.1 (by norm_num) (by norm_num)
  have o4 := odd_conj (r := 13) (p := 5) (h := 14) (t := 4) (ord := 14) (cs := 1344)
    (cg := (cgL 5 2).toArray) (cgInv := (cgL 5 2).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.1 (by decide) kconj.2.2.2.1 (by norm_num)
    (by norm_num)
  have o5 := odd_conj (r := 15) (p := 3) (h := 16) (t := 4) (ord := 10) (cs := 1120)
    (cg := (cgL 5 2).toArray) (cgInv := (cgL 5 2).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.1 (by decide) kconj.2.2.2.2.1 (by norm_num)
    (by norm_num)
  have hrep : mclSift (mclCentTbl 4) = true := by
    rw [siftF (by norm_num)]
    exact kreps.2.2.1
  unfold CFSG.Sporadic.SmallOddCore.classOK
  simp only [e, recR1.1, recK1.1, recQ1a.1, recQ1b.1, recQ1c.1, recQ1d.1, recQ1e.1, recR1.2.1,
    recR1.2.2, recK1.2.1, recK1.2.2, recQ1a.2.1, recQ1b.2.1, recQ1c.2.1, recQ1d.2.1, recQ1e.2.1,
    s1a, s1b, permF (k := 4) (by norm_num), invol_of (k := 4) (by norm_num) kreps.1, hrep,
    cg_all 5 2 4 (by norm_num) (by norm_num) kcg.1, o1, o2, o3, o4, o5, sel1, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, ↓reduceIte,
    Bool.and_true, Bool.or_false, beq_self_eq_true, Bool.false_eq_true]

theorem row2 : CFSG.Sporadic.SmallOddCore.classOK 275 898128000 120000 mclPGTbls mclPGInvTbls
    mclSift mclOuterTbl
    { rep := mclCentTbl 17, outer := true, classSize := 113400,
      centOrder := 7920, centGens := [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21],
      oddPrimes := [3, 5, 11], odd := [
        { rep := mclCentTbl 22, prime := 5, classSize := 1584, wit := .conj (mclCentTbl 23) 4 },
        { rep := mclCentTbl 24, prime := 11, classSize := 720, wit := .conj (mclCentTbl 25) 8 },
        { rep := mclCentTbl 26, prime := 11, classSize := 720, wit := .conj (mclCentTbl 27) 8 },
        { rep := mclCentTbl 28, prime := 3, classSize := 440, wit := .conj (mclCentTbl 29) 2 }] }
    (conjClosureH 275 mclPGTbls mclPGInvTbls (mclCentTbl 17) 120000) = true := by
  have e : [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21] = cgL 18 4 := rfl
  have o1 := odd_conj (r := 22) (p := 5) (h := 23) (t := 17) (ord := 4) (cs := 1584)
    (cg := (cgL 18 4).toArray) (cgInv := (cgL 18 4).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.1 (by decide) kconj.2.2.2.2.2.1 (by norm_num)
    (by norm_num)
  have o2 := odd_conj (r := 24) (p := 11) (h := 25) (t := 17) (ord := 8) (cs := 720)
    (cg := (cgL 18 4).toArray) (cgInv := (cgL 18 4).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.1 (by decide) kconj.2.2.2.2.2.2.1 (by norm_num)
    (by norm_num)
  have o3 := odd_conj (r := 26) (p := 11) (h := 27) (t := 17) (ord := 8) (cs := 720)
    (cg := (cgL 18 4).toArray) (cgInv := (cgL 18 4).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.2.1 (by decide) kconj.2.2.2.2.2.2.2.1
    (by norm_num) (by norm_num)
  have o4 := odd_conj (r := 28) (p := 3) (h := 29) (t := 17) (ord := 2) (cs := 440)
    (cg := (cgL 18 4).toArray) (cgInv := (cgL 18 4).toArray.map (invT 275)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.2.2 (by decide) kconj.2.2.2.2.2.2.2.2
    (by norm_num) (by norm_num)
  have hrep : (!mclSift (mclCentTbl 17) && mclSift (compT 275 (mclCentTbl 17) mclOuterTbl)) =
      true := by
    rw [siftF (by norm_num), u_tab, tabF (by norm_num), compT_unpack (Fc (by norm_num))
      (Fc (by norm_num)), sift_eq (compF (Fc (by norm_num)) (Fc (by norm_num))),
      notB (b := sK (F 17)) kreps.2.2.2.1]
    exact kreps.2.2.2.2
  unfold CFSG.Sporadic.SmallOddCore.classOK
  simp only [e, recR2.1, recK2.1, recQ2a.1, recQ2b.1, recQ2c.1, recQ2d.1, recR2.2.1, recR2.2.2,
    recK2.2.1, recK2.2.2, recQ2a.2.1, recQ2b.2.1, recQ2c.2.1, recQ2d.2.1, s2a, s2b,
    permF (k := 17) (by norm_num), invol_of (k := 17) (by norm_num) kreps.2.1, hrep,
    cg_all 18 4 17 (by norm_num) (by norm_num) kcg.2, o1, o2, o3, o4, sel2, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, ↓reduceIte,
    Bool.and_true, Bool.or_false, beq_self_eq_true]

theorem scov_all : (hRec 275 9 MN.SY.cnt MN.SY.T MN.SY.PL).1.all (fun s => !involOK 275 s ||
    (memT 275 (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).1 s ||
      memT 275 (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).1 s)) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR sy_pe i hi'
  rw [rec_get hi, involF hc]
  have h := allN_spec k_scov i hi'
  unfold scovK at h
  rw [strictB_eq''] at h
  cases hs : involK (MN.SY.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR r1_pe) hc h1)
    · exact Or.inr (mem_at (canonR r2_pe) hc h1)

theorem kucov : ucovK 0 4 = true ∧ ucovK 1 17 = true := by
  simpa only [bAnd_iff] using k_ucov

theorem ucov_of {i t : Nat} (ht : t < 30) (h : ucovK i t = true) :
    (memT 275 (hRec 275 9 MN.R1.cnt MN.R1.T MN.R1.PL).1
        (conjT 275 mclOuterTbl (invT 275 mclOuterTbl) (mclCentTbl t)) ||
      memT 275 (hRec 275 9 MN.R2.cnt MN.R2.T MN.R2.PL).1
        (conjT 275 mclOuterTbl (invT 275 mclOuterTbl) (mclCentTbl t))) = true := by
  have hu : mclOuterTbl = mclCentTbl 0 := rfl
  rw [hu, invF (by norm_num), tabF (by norm_num), tabF ht,
    conjT_unpack (Fc (by norm_num)) (Ic (by norm_num)) (Fc ht)]
  have hy := compF (compF (Fc (k := 0) (by norm_num)) (Fc ht)) (Ic (k := 0) (by norm_num))
  unfold ucovK at h
  rw [strictB_eq''] at h
  simp only [Bool.or_eq_true]
  rcases bIf_or' h with h1 | h1
  · exact Or.inl (mem_at (canonR r1_pe) hy h1)
  · exact Or.inr (mem_at (canonR r2_pe) hy h1)

@[expose] noncomputable def noneK (k : Nat) (f : Nat → Bool) : Bool :=
  allN k (fun j => bIf(f j, false, true))

theorem k_stab : bAnd(allN 13 (fun j => canonK 275 9 (mask 9) (275 * 9) (S j)),
    bAnd(allN 13 (fun j => bIf(Nat.beq (pg 9 (mask 9) (S j) 0) 0, sK (S j), true)),
    allN 275 (fun x => bIf(Nat.beq x 0, true, bIf(noneK 13 (fun j =>
      bAnd(Nat.beq (pg 9 (mask 9) (S j) 0) 0,
        bIf(Nat.beq (pg 9 (mask 9) (S j) x) x, false, true))), false, true))))) = true := by
  quickRfl

theorem stab_facts : allN 13 (fun j => canonK 275 9 (mask 9) (275 * 9) (S j)) = true ∧
    allN 13 (fun j => bIf(Nat.beq (pg 9 (mask 9) (S j) 0) 0, sK (S j), true)) = true ∧
    allN 275 (fun x => bIf(Nat.beq x 0, true, bIf(noneK 13 (fun j =>
      bAnd(Nat.beq (pg 9 (mask 9) (S j) 0) 0,
        bIf(Nat.beq (pg 9 (mask 9) (S j) x) x, false, true))), false, true))) = true := by
  simpa only [bAnd_iff] using k_stab

theorem strong_tab {j : Nat} (hj : j < 13) :
    (CFSG.Sporadic.Schreier.mclStrongArrs)[j]!.map UInt32.ofNat =
      tabT (unpack 275 9 (S j)) := by
  rw [CertificateChecks.KernelCensus.McLK.binds.2.2.2.2.1 j hj]
  rfl

theorem ap_S {j x : Nat} (hj : j < 13) (hx : x < 275) :
    ap (tabT (unpack 275 9 (S j))) x = pg 9 (mask 9) (S j) x := by
  rw [ap_tabT _ (unpack_lt (allN_spec stab_facts.1 j hj)), CFSG.KC.Misc.PairCount.unpack_get hx]

theorem stab_mem {s : Table} (hs : s ∈ ((List.range 13).map fun j =>
    (CFSG.Sporadic.Schreier.mclStrongArrs)[j]!.map UInt32.ofNat)) :
    ∃ j < 13, s = tabT (unpack 275 9 (S j)) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
  exact ⟨j, List.mem_range.1 hj, strong_tab (List.mem_range.1 hj)⟩

theorem stab_ok : mclStabOK = true := by
  unfold mclStabOK mclStabTbls
  simp only [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro s hs
    rw [List.mem_filter] at hs
    obtain ⟨hm, hp⟩ := hs
    obtain ⟨j, hj, rfl⟩ := stab_mem hm
    rw [ap_S hj (by norm_num)] at hp
    have h := allN_spec stab_facts.2.1 j hj
    have hb : Nat.beq (pg 9 (mask 9) (S j) 0) 0 = true := by simpa using hp
    rw [hb] at h
    rw [sift_eq (allN_spec stab_facts.1 j hj), ap_S hj (by norm_num)]
    simp only [Bool.and_eq_true]
    exact ⟨h, hp⟩
  · rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    have h := allN_spec stab_facts.2.2 x hx'
    cases e : Nat.beq x 0
    · rw [e] at h
      have hn := notB h
      unfold noneK at hn
      have hex : ∃ j < 13, bAnd(Nat.beq (pg 9 (mask 9) (S j) 0) 0,
          bIf(Nat.beq (pg 9 (mask 9) (S j) x) x, false, true)) = true := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have : allN 13 (fun j => bIf(bAnd(Nat.beq (pg 9 (mask 9) (S j) 0) 0,
            bIf(Nat.beq (pg 9 (mask 9) (S j) x) x, false, true)), false, true)) = true := by
          rw [allN_iff]
          intro j hj
          have := hne j hj
          revert this
          cases bAnd(Nat.beq (pg 9 (mask 9) (S j) 0) 0,
            bIf(Nat.beq (pg 9 (mask 9) (S j) x) x, false, true)) <;> simp
        rw [this] at hn
        exact absurd hn (by decide)
      obtain ⟨j, hj, hjx⟩ := hex
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hjx
      have hne1 : x ≠ 0 := fun h1 => by
        rw [h1] at e
        exact absurd e (by decide)
      have hxe : (x == 0) = false := by simp [hne1]
      simp only [hxe, Bool.false_or, List.any_eq_true, List.mem_filter]
      refine ⟨_, ⟨List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩, ?_⟩
      · rw [strong_tab hj, ap_S hj (by norm_num), Nat.eq_of_beq_eq_true h1]
        rfl
      · rw [strong_tab hj, ap_S hj hx', bne_iff_ne]
        intro hq
        rw [hq, Nat.beq_refl] at h2
        exact absurd h2 (by decide)
    · have : x = 0 := Nat.eq_of_beq_eq_true e
      subst this
      rfl


theorem facts2284 : (mclStabOK = true) ∧
    (centDataOK 275 898128000 120000 mclPGTbls mclPGInvTbls mclSift mclOuterTbl mclSylowGenTbls
      mclSylowOrder mclRows = true) := by
  refine ⟨stab_ok, ?_⟩
  unfold centDataOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨syl_ok, ?_⟩, ?_⟩
  · simp only [mclRows, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨row1, row2⟩
  · unfold coverOK
    simp only [mclRows, sy_eq, recSY.1, recR1.1, recR2.1, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false,
      Bool.and_eq_true]
    exact ⟨scov_all, ucov_of (by norm_num) kucov.1, ucov_of (by norm_num) kucov.2⟩

end CertificateChecks.KernelSpor.MNd

end
