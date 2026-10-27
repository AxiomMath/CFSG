
module

public import Certificates.Kernel.Sporadic.ON4.JCard
public import Certificates.Kernel.Sporadic.ON3.Sift
public import Certificates.Kernel.Sporadic.ON3.Small
public import Certificates.Kernel.Sporadic.ON4.Sx0
public import Certificates.Kernel.Sporadic.ON4.Sx1
public import Certificates.Kernel.Sporadic.ON4.Sx2
public import Certificates.Kernel.Sporadic.ON4.Sx3
public import Certificates.Kernel.Sporadic.ON4.Sm
public import Certificates.Kernel.Sporadic.ON4.St0
public import Certificates.Kernel.Sporadic.ON4.St1a
public import Certificates.Kernel.Sporadic.ON4.St1b
public import CFSG.Certificates.Kernel.Spor.ChainSKSound
public import CFSG.Certificates.Kernel.Spor.ChainKSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON4K.xMAll CertificateChecks.KernelSpor.ON4K.xMS 48
#kon_join CertificateChecks.KernelSpor.ON4K.pxAll CertificateChecks.KernelSpor.ON4K.pxS 8
#kon_join CertificateChecks.KernelSpor.ON4K.posCAll CertificateChecks.KernelSpor.ON4K.posCS 24
#kon_join CertificateChecks.KernelSpor.ON4K.ptC0All CertificateChecks.KernelSpor.ON4K.ptC0 15
#kon_join CertificateChecks.KernelSpor.ON4K.ptC1All CertificateChecks.KernelSpor.ON4K.ptC1 21
#kon_join CertificateChecks.KernelSpor.ON4K.ptC2All CertificateChecks.KernelSpor.ON4K.ptC2 1
#kon_join CertificateChecks.KernelSpor.ON4K.sch0All CertificateChecks.KernelSpor.ON4K.sch0 15
#kon_join CertificateChecks.KernelSpor.ON4K.sch1All CertificateChecks.KernelSpor.ON4K.sch1 42
#kon_join CertificateChecks.KernelSpor.ON4K.sch2All CertificateChecks.KernelSpor.ON4K.sch2 1
#kon_join CertificateChecks.KernelSpor.ON4K.tree0All CertificateChecks.KernelSpor.ON4K.tree0 120
#kon_join CertificateChecks.KernelSpor.ON4K.tree1All CertificateChecks.KernelSpor.ON4K.tree1 26
#kon_join CertificateChecks.KernelSpor.ON4K.tree2All CertificateChecks.KernelSpor.ON4K.tree2 36

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.KS.TW CFSG.KS.PW CFSG.ONSchreier
open CFSG.ONSchreier.Native CertificateChecks.KernelSpor.ON3
open CFSG.Sporadic.ON.Native (nPts)

theorem px_all {x : Nat} (hx : x < 245520) : pxAt 1152 xT pT x = true ∧
    pxAt 27120 xM pM x = true ∧ (x < 1152 → xTAt x = true) := by
  have hs : x / 30690 < 8 := by omega
  have h := allN_spec (pxAll (x / 30690) hs) (x % 30690) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 30690) 30690) (x % 30690) = x := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  simp only [strictB_eq''] at h
  rw [e] at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hx' => ?_⟩
  rw [blt_of hx'] at h3
  exact h3

theorem xM_all {i : Nat} (hi : i < 27120) : xMAt i = true := by
  have hs : i / 565 < 48 := by omega
  have h := allN_spec (xMAll (i / 565) hs) (i % 565) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 565) 565) (i % 565) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  exact h

theorem xM_parts {i : Nat} (hi : i < 27120) : xAt 27120 5 3 xM pM iM iMI mG dM i = true ∧
    xAt 27120 4 2 xM pM iL iLI lG dL i = true ∧ xAt 27120 5 3 xM pM iMc iMcI mcO dMc i = true ∧
    xAt 27120 6 3 xM pM iLc iLcI lcO dLc i = true := by
  have h := xM_all hi
  unfold xMAt at h
  simp only [bAnd_iff] at h
  exact h

theorem t_words : ∀ j, 6 ≤ j → j < 8 → LetM j (wordL.getD (Nat.add 11 j) []) ∧
    (∀ x < 245520, tF j x = (wordL.getD (Nat.add 11 j) []).foldr (GZ tF tFI) x) ∧
    ∀ i, dT j i = (wordL.getD (Nat.add 11 j) []).foldr (GZ iT iTI) i := by
  intro j h6 h8
  interval_cases j
  · refine ⟨strong_lets.1, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : tF 6 x = tS6 x := rfl
    rw [a1, tS6_eq]
    exact foldr_congr (m := 6) (fun i hi => by rw [tF_lo (by omega), tG7_lo hi])
      (fun i hi => by rw [tFI_lo (by omega), tGI7_lo hi]) _ strong_lets.1 x
  · refine ⟨strong_lets.2.1, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : tF 7 x = tS7 x := rfl
    rw [a1, tS7_eq]
    exact foldr_congr (m := 7) (fun i hi => by rw [tF_lo hi]) (fun i hi => by rw [tFI_lo hi]) _
      strong_lets.2.1 x

theorem fastT : tFX = tF ∧ tFIX = tFI :=
  fastX_eq (s := 8) (m := 6) (O := tG) (D := dT) (W := fun j => wordL.getD (Nat.add 11 j) [])
    tF_pair (fun i hi => (px_all (by omega : i < 245520)).2.2 hi) (fun x hx => (px_all hx).1)
    (fun j hj y _ => by rw [tF_lo (by omega), tG7_lo hj]) t_words

theorem m_words : ∀ j, 3 ≤ j → j < 5 → LetM j (wordL.getD (Nat.add 16 j) []) ∧
    (∀ x < 245520, mF j x = (wordL.getD (Nat.add 16 j) []).foldr (GZ mF mFI) x) ∧
    ∀ i, dM j i = (wordL.getD (Nat.add 16 j) []).foldr (GZ iM iMI) i := by
  intro j h3 h5
  interval_cases j
  · refine ⟨strong_lets.2.2.1, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : mF 3 x = mS3 x := rfl
    rw [a1, mS3_eq]
    exact foldr_congr (m := 3) (fun i hi => by rw [mF_lo (by omega), mG4_lo hi])
      (fun i hi => by rw [mFI_lo (by omega), mGI4_lo hi]) _ strong_lets.2.2.1 x
  · refine ⟨strong_lets.2.2.2.1, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : mF 4 x = mS4 x := rfl
    rw [a1, mS4_eq]
    exact foldr_congr (m := 4) (fun i hi => by rw [mF_lo hi]) (fun i hi => by rw [mFI_lo hi]) _
      strong_lets.2.2.2.1 x

theorem fastM : mFX = mF ∧ mFIX = mFI :=
  fastX_eq (s := 5) (m := 3) (O := mG) (D := dM) (W := fun j => wordL.getD (Nat.add 16 j) [])
    mF_pair (fun i hi => (xM_parts hi).1) (fun x hx => (px_all hx).2.1)
    (fun j hj y _ => by rw [mF_lo (by omega), mG4_lo hj]) m_words

theorem l_words : ∀ j, 2 ≤ j → j < 4 → LetM j (wordL.getD (Nat.add 19 j) []) ∧
    (∀ x < 245520, lF j x = (wordL.getD (Nat.add 19 j) []).foldr (GZ lF lFI) x) ∧
    ∀ i, dL j i = (wordL.getD (Nat.add 19 j) []).foldr (GZ iL iLI) i := by
  intro j h2 h4
  interval_cases j
  · refine ⟨strong_lets.2.2.2.2.1, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : lF 2 x = lS2 x := rfl
    rw [a1, lS2_eq]
    exact foldr_congr (m := 2) (fun i hi => by rw [lF_lo (by omega), lG3_lo hi])
      (fun i hi => by rw [lFI_lo (by omega), lGI3_lo hi]) _ strong_lets.2.2.2.2.1 x
  · refine ⟨strong_lets.2.2.2.2.2, fun x _ => ?_, fun i => tr_word _ _ (by norm_num) i⟩
    have a1 : lF 3 x = lS3 x := rfl
    rw [a1, lS3_eq]
    exact foldr_congr (m := 3) (fun i hi => by rw [lF_lo hi]) (fun i hi => by rw [lFI_lo hi]) _
      strong_lets.2.2.2.2.2 x

theorem fastL : lFX = lF ∧ lFIX = lFI :=
  fastX_eq (s := 4) (m := 2) (O := lG) (D := dL) (W := fun j => wordL.getD (Nat.add 19 j) [])
    lF_pair (fun i hi => (xM_parts hi).2.1) (fun x hx => (px_all hx).2.1)
    (fun j hj y _ => by rw [lF_lo (by omega), lG3_lo hj]) l_words

theorem fastMc : mcFX = mcF ∧ mcFIX = mcFI :=
  fastX_eq (s := 5) (m := 3) (O := mcO) (D := dMc) (W := fun j => Data.McommChain.strongWords[j]!)
    mcF_pair (fun i hi => (xM_parts hi).2.2.1) (fun x hx => (px_all hx).2.1)
    (fun j hj y _ => by rw [(mc_lo hj).1])
    (fun j h3 h5 => ⟨(mc_words j h3 h5).1, (mc_words j h3 h5).2, fun i => by
      interval_cases j
      · exact tr4_word _ _ (k := 0) (by norm_num) i
      · exact tr4_word _ _ (k := 1) (by norm_num) i⟩)

theorem fastLc : lcFX = lcF ∧ lcFIX = lcFI :=
  fastX_eq (s := 6) (m := 3) (O := lcO) (D := dLc) (W := fun j => Data.LcommChain.strongWords[j]!)
    lcF_pair (fun i hi => (xM_parts hi).2.2.2) (fun x hx => (px_all hx).2.1)
    (fun j hj y _ => by rw [(lc_lo hj).1])
    (fun j h3 h6 => ⟨(lc_words j h3 h6).1, (lc_words j h3 h6).2, fun i => by
      interval_cases j
      · exact tr4_word _ _ (k := 2) (by norm_num) i
      · exact tr4_word _ _ (k := 3) (by norm_num) i
      · exact tr4_word _ _ (k := 4) (by norm_num) i⟩)

theorem local_of {orig : Array (Array Nat)} {ch : Data.BigChain} {s : Nat} {F : Nat → Nat → Nat}
    (hS : (extendStrong nPts orig ch.strongWords).size = s ∧
      ∀ j < s, (extendStrong nPts orig ch.strongWords)[j]! = Array.ofFn (n := 245520) fun i => F j i.val)
    (hm : orig.size ≤ s) (hO : ∀ j < orig.size, orig[j]! = Array.ofFn (n := 245520) fun i => F j i.val)
    (hpc : pointChainOK nPts orig.size (extendStrong nPts orig ch.strongWords) ch.base
      ch.strongWords 4 = true)
    (hsz : cOrbitSizes nPts (extendStrong nPts orig ch.strongWords) ch.base = ch.orbitSizes.toList) :
    localChainOK orig ch = true := by
  unfold localChainOK
  rw [hpc, hsz]
  simp only [Bool.and_true, beq_self_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by rw [hS.1]; exact hm, allBelowN_iff.2 fun j hj => ?_⟩
  rw [hS.2 j (by omega), hO j hj]
  unfold peq
  exact allBelowN_iff.2 fun i _ => beq_self_eq_true _

theorem base3 (b : Array Nat) (hb : b = Data.TChain.base) :
    b.size = 3 ∧ ∀ k < 3, b[k]! = bB k ∧ bB k < 245520 := by
  subst hb
  exact base_facts

theorem schC_all {c i : Nat} (hc : c < 5) (hi : i < 3) :
    ∀ h < 16 * nat3 15 42 1 i, schC c i (h / 16) = true := by
  intro h hh
  interval_cases i
  · have h1 : h < 240 := hh
    have h2 : h / 16 < 15 := by omega
    exact allN_spec (sch0All (h / 16) h2) c hc
  · have h1 : h < 672 := hh
    have h2 : h / 16 < 42 := by omega
    exact allN_spec (sch1All (h / 16) h2) c hc
  · have h1 : h < 16 := hh
    have h2 : h / 16 < 1 := by omega
    exact allN_spec (sch2All (h / 16) h2) c hc

theorem schC_pt {c i h : Nat} (hc : c < 5) (hi : i < 3) (hh : h < 16 * nat3 15 42 1 i) :
    (fun h => bIf(Nat.beq c 0, bIf(Nat.blt h (tMr i), allN (Nat.mul 2 (tLEN i)) fun j =>
      schK (fun i => stepX tFX tFIX (tIDX i) (tLEN i)) (fun i => invX tFX tFIX (tIDX i) (tLEN i))
        tPTS tPOS tPAR tLAB tMr bB i h j, true),
  bIf(Nat.beq c 1, bIf(Nat.blt h (mMr i), allN (Nat.mul 2 (mLEN i)) fun j =>
      schK (fun i => stepX mFX mFIX (mIDX i) (mLEN i)) (fun i => invX mFX mFIX (mIDX i) (mLEN i))
        mPTS mPOS mPAR mLAB mMr bB i h j, true),
  bIf(Nat.beq c 2, bIf(Nat.blt h (lMr i), allN (Nat.mul 2 (lLEN i)) fun j =>
      schK (fun i => stepX lFX lFIX (lIDX i) (lLEN i)) (fun i => invX lFX lFIX (lIDX i) (lLEN i))
        lPTS lPOS lPAR lLAB lMr bB i h j, true),
  bIf(Nat.beq c 3, bIf(Nat.blt h (mcMr i), allN (Nat.mul 2 (mcLEN i)) fun j =>
      schK (fun i => stepX mcFX mcFIX (mcIDX i) (mcLEN i))
        (fun i => invX mcFX mcFIX (mcIDX i) (mcLEN i)) mcPTS mcPOS mcPAR mcLAB mcMr bB i h j, true),
    bIf(Nat.blt h (lcMr i), allN (Nat.mul 2 (lcLEN i)) fun j =>
      schK (fun i => stepX lcFX lcFIX (lcIDX i) (lcLEN i))
        (fun i => invX lcFX lcFIX (lcIDX i) (lcLEN i)) lcPTS lcPOS lcPAR lcLAB lcMr bB i h j,
      true)))))) h = true := by
  have hs := schC_all hc hi h hh
  unfold schC at hs
  have h2 := allN_spec hs (h % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (h / 16) 16) (h % 16) = h := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e, strictB_eq''] at h2
  exact h2

theorem chain_ok {orig : Array (Array Nat)} {ch : Data.BigChain} {m s : Nat}
    {F FI : Nat → Nat → Nat} {LEN : Nat → Nat} {IDX : Nat → Nat → Nat} {Mr : Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hm : orig.size = m) (hms : m ≤ s) (hWs : ch.strongWords.size = s)
    (hb : ch.base = Data.TChain.base)
    (hS : (extendStrong nPts orig ch.strongWords).size = s ∧ ∀ j < s,
      (extendStrong nPts orig ch.strongWords)[j]! = Array.ofFn (n := 245520) fun i => F j i.val)
    (hO : ∀ j < m, orig[j]! = Array.ofFn (n := 245520) fun i => F j i.val)
    (hp : InvPair 245520 s F FI)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ ch.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < 245520, F j x = ch.strongWords[j]!.foldr (GZ F FI) x)
    (hidx : ∀ i < 3, idxOK F s bB i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead 245520 (Mr i) (bB i) (PTS i) (PAR i) (LAB i) = true)
    (hpt : ∀ i < 3, ∀ k < Mr i, cbPt 245520 (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < 245520, cbPos 245520 (Mr i) (PTS i) (POS i) z = true)
    (hsch : ∀ i < 3, ∀ h < Mr i, ∀ j < Nat.mul 2 (LEN i),
      schK (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS PAR
        LAB Mr bB i h j = true)
    (hsz : [Mr 0, Mr 1, Mr 2] = ch.orbitSizes.toList) : localChainOK orig ch = true := by
  obtain ⟨hb1, hb2⟩ := base3 ch.base hb
  obtain ⟨pc, sz⟩ := pointChain3_sound (n := 245520) (chunks := 4) hS.1 hWs hms
    (strong_facts hS hp) hW hb1 hb2 hidx hh hpt hz hsch
  refine local_of hS (by rw [hm]; exact hms) (fun j hj => hO j (by rw [← hm]; exact hj)) ?_
    (sz.trans hsz)
  rw [hm]
  exact pc

theorem sch_from {F FI FX FIX : Nat → Nat → Nat} {LEN : Nat → Nat} {IDX : Nat → Nat → Nat}
    {Mr : Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat} (hF : FX = F) (hFI : FIX = FI)
    (hb : ∀ i < 3, Mr i ≤ 16 * nat3 15 42 1 i)
    (hpt : ∀ i < 3, ∀ h < 16 * nat3 15 42 1 i, bIf(Nat.blt h (Mr i), allN (Nat.mul 2 (LEN i)) fun j =>
      schK (fun i => stepX FX FIX (IDX i) (LEN i)) (fun i => invX FX FIX (IDX i) (LEN i)) PTS POS PAR
        LAB Mr bB i h j, true) = true) :
    ∀ i < 3, ∀ h < Mr i, ∀ j < Nat.mul 2 (LEN i),
      schK (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS PAR
        LAB Mr bB i h j = true := by
  intro i hi h hh j hj
  have h2 := hpt i hi h (by have := hb i hi; omega)
  rw [blt_of hh, hF, hFI] at h2
  exact allN_spec h2 j hj

theorem sizes4 : mcMr 0 = 240 ∧ mcMr 1 = 336 ∧ mcMr 2 = 1 ∧ lcMr 0 = 240 ∧ lcMr 1 = 336 ∧
    lcMr 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem t_ok : localChainOK (wordArrs Data.TWords) Data.TChain = true := by
  obtain ⟨s0, s1, s2, -⟩ := sizes
  refine chain_ok (m := 6) (s := 8) (F := tF) (FI := tFI) (LEN := tLEN) (IDX := tIDX) (Mr := tMr)
    (PTS := tPTS) (POS := tPOS) (PAR := tPAR) (LAB := tLAB) twords_size (by norm_num) rfl rfl
    tStrong_get (fun j hj => arr_ext (wordArrs_size_get (Nat.lt_of_lt_of_eq hj rfl))
      fun y hy => by rw [tw_get hj y hy, tF_lo (by omega), tG7_lo hj]) tF_pair
    (fun j h6 h8 => by
      interval_cases j
      · exact ⟨(t_words 6 (by norm_num) (by norm_num)).1, (t_words 6 (by norm_num) (by norm_num)).2.1⟩
      · exact ⟨(t_words 7 (by norm_num) (by norm_num)).1, (t_words 7 (by norm_num) (by norm_num)).2.1⟩)
    (fun i hi => (heads hi).1) (fun i hi => (heads hi).2.2.2.1) (fun i hi => ptT_all hi)
    (fun i hi => posT_all hi)
    (sch_from fastT.1 fastT.2 (fun i hi => by interval_cases i <;> simp only [s0, s1, s2] <;> decide)
      fun i hi h hh => schC_pt (c := 0) (by norm_num) hi hh) (by rw [s0, s1, s2]; rfl)

theorem m_ok : localChainOK (wordArrs Data.MWords) Data.MChain = true := by
  obtain ⟨-, -, -, s0, s1, s2, -⟩ := sizes
  refine chain_ok (m := 3) (s := 5) (F := mF) (FI := mFI) (LEN := mLEN) (IDX := mIDX) (Mr := mMr)
    (PTS := mPTS) (POS := mPOS) (PAR := mPAR) (LAB := mLAB)
    (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) (by norm_num) rfl rfl
    mStrong_get (fun j hj => arr_ext (wordArrs_size_get (Nat.lt_of_lt_of_eq hj rfl))
      fun y hy => by rw [(m_get hj y hy).1, mF_lo (by omega), mG4_lo hj]) mF_pair
    (fun j h3 h5 => by
      interval_cases j
      · exact ⟨(m_words 3 (by norm_num) (by norm_num)).1, (m_words 3 (by norm_num) (by norm_num)).2.1⟩
      · exact ⟨(m_words 4 (by norm_num) (by norm_num)).1, (m_words 4 (by norm_num) (by norm_num)).2.1⟩)
    (fun i hi => (heads hi).2.1) (fun i hi => (heads hi).2.2.2.2.1) (fun i hi => ptM_all hi)
    (fun i hi => posM_all hi)
    (sch_from fastM.1 fastM.2 (fun i hi => by interval_cases i <;> simp only [s0, s1, s2] <;> decide)
      fun i hi h hh => schC_pt (c := 1) (by norm_num) hi hh) (by rw [s0, s1, s2]; rfl)

theorem l_ok : localChainOK (wordArrs Data.LWords) Data.LChain = true := by
  obtain ⟨-, -, -, -, -, -, s0, s1, s2⟩ := sizes
  refine chain_ok (m := 2) (s := 4) (F := lF) (FI := lFI) (LEN := lLEN) (IDX := lIDX) (Mr := lMr)
    (PTS := lPTS) (POS := lPOS) (PAR := lPAR) (LAB := lLAB)
    (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) (by norm_num) rfl rfl
    lStrong_get (fun j hj => arr_ext (wordArrs_size_get (Nat.lt_of_lt_of_eq hj rfl))
      fun y hy => by rw [(l_get hj y hy).1, lF_lo (by omega), lG3_lo hj]) lF_pair
    (fun j h2 h4 => by
      interval_cases j
      · exact ⟨(l_words 2 (by norm_num) (by norm_num)).1, (l_words 2 (by norm_num) (by norm_num)).2.1⟩
      · exact ⟨(l_words 3 (by norm_num) (by norm_num)).1, (l_words 3 (by norm_num) (by norm_num)).2.1⟩)
    (fun i hi => (heads hi).2.2.1) (fun i hi => (heads hi).2.2.2.2.2) (fun i hi => ptL_all hi)
    (fun i hi => posL_all hi)
    (sch_from fastL.1 fastL.2 (fun i hi => by interval_cases i <;> simp only [s0, s1, s2] <;> decide)
      fun i hi h hh => schC_pt (c := 2) (by norm_num) hi hh) (by rw [s0, s1, s2]; rfl)

theorem heads4 {i : Nat} (hi : i < 3) : idxOK mcF 5 bB i (mcIDX i) (mcLEN i) = true ∧
    idxOK lcF 6 bB i (lcIDX i) (lcLEN i) = true ∧ idxOK jF 9 bB i (jIDX i) (jLEN i) = true ∧
    cbHead 245520 (mcMr i) (bB i) (mcPTS i) (mcPAR i) (mcLAB i) = true ∧
    cbHead 245520 (lcMr i) (bB i) (lcPTS i) (lcPAR i) (lcLAB i) = true := by
  have h := allN_spec heads_ok i hi
  simp only [bAnd_iff] at h
  rw [fastMc.1, fastLc.1] at h
  exact h

theorem ptC_parts {i s : Nat} (h : ptC i s = true) :
    cbPtRange 245520 (mcMr i) (Nat.mul 2 (mcLEN i)) (stepX mcFX mcFIX (mcIDX i) (mcLEN i))
      (mcPTS i) (mcPOS i) (mcPAR i) (mcLAB i) (Nat.mul s 16) 16 = true ∧
    cbPtRange 245520 (lcMr i) (Nat.mul 2 (lcLEN i)) (stepX lcFX lcFIX (lcIDX i) (lcLEN i))
      (lcPTS i) (lcPOS i) (lcPAR i) (lcLAB i) (Nat.mul s 16) 16 = true := by
  unfold ptC at h
  exact (bAnd_iff _ _).1 h

theorem ptCs {i : Nat} (hi : i < 3) : ∀ s < nat3 15 21 1 i, ptC i s = true := by
  intro s hs
  interval_cases i
  · exact ptC0All s hs
  · exact ptC1All s hs
  · exact ptC2All s hs

theorem ptMc_all {i : Nat} (hi : i < 3) : ∀ k < mcMr i, cbPt 245520 (mcMr i) (Nat.mul 2 (mcLEN i))
    (stepX mcF mcFI (mcIDX i) (mcLEN i)) (mcPTS i) (mcPOS i) (mcPAR i) (mcLAB i) k = true := by
  rw [← fastMc.1, ← fastMc.2]
  obtain ⟨s0, s1, s2, -⟩ := sizes4
  refine pt_of (NS := nat3 15 21 1 i) (fun s hs => (ptC_parts (ptCs hi s hs)).1) (fun _ => rfl) ?_
  interval_cases i <;> simp only [s0, s1, s2] <;> decide

theorem ptLc_all {i : Nat} (hi : i < 3) : ∀ k < lcMr i, cbPt 245520 (lcMr i) (Nat.mul 2 (lcLEN i))
    (stepX lcF lcFI (lcIDX i) (lcLEN i)) (lcPTS i) (lcPOS i) (lcPAR i) (lcLAB i) k = true := by
  rw [← fastLc.1, ← fastLc.2]
  obtain ⟨-, -, -, s0, s1, s2⟩ := sizes4
  refine pt_of (NS := nat3 15 21 1 i) (fun s hs => (ptC_parts (ptCs hi s hs)).2) (fun _ => rfl) ?_
  interval_cases i <;> simp only [s0, s1, s2] <;> decide

theorem posCS_eq (s i : Nat) (hs : s < 8) : posCS (s + 8 * i) =
    allN (nat_lit 30690) fun d => strictB (Nat.add (Nat.mul s (nat_lit 30690)) d) fun z =>
      bAnd(cbPos 245520 (mcMr i) (mcPTS i) (mcPOS i) z, cbPos 245520 (lcMr i) (lcPTS i) (lcPOS i) z) := by
  unfold posCS
  simp only [strictB_eq'']
  have e1 : Nat.mod (s + 8 * i) 8 = s := by
    change (s + 8 * i) % 8 = s
    omega
  have e2 : Nat.div (s + 8 * i) 8 = i := by
    change (s + 8 * i) / 8 = i
    omega
  rw [e1, e2]

theorem posC4 {i : Nat} (hi : i < 3) : ∀ z < 245520,
    cbPos 245520 (mcMr i) (mcPTS i) (mcPOS i) z = true ∧
    cbPos 245520 (lcMr i) (lcPTS i) (lcPOS i) z = true := by
  intro z hz
  have hs : z / 30690 < 8 := by omega
  have hu : z / 30690 + 8 * i < 24 := by omega
  have h := posCAll _ hu
  rw [posCS_eq _ _ hs] at h
  have h' := allN_spec h (z % 30690) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (z / 30690) 30690) (z % 30690) = z := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e, strictB_eq''] at h'
  exact (bAnd_iff _ _).1 h'

theorem mc_ok : localChainOK (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs)
    Data.McommChain = true := by
  obtain ⟨s0, s1, s2, -⟩ := sizes4
  refine chain_ok (m := 3) (s := 5) (F := mcF) (FI := mcFI) (LEN := mcLEN) (IDX := mcIDX)
    (Mr := mcMr) (PTS := mcPTS) (POS := mcPOS) (PAR := mcPAR) (LAB := mcLAB)
    mcOrig_get.1 (by norm_num) rfl rfl mcStrong_get
    (fun j hj => by rw [mcOrig_get.2 j hj, (mc_lo hj).1]) mcF_pair mc_words
    (fun i hi => (heads4 hi).1) (fun i hi => (heads4 hi).2.2.2.1) (fun i hi => ptMc_all hi)
    (fun i hi z hz => (posC4 hi z hz).1)
    (sch_from fastMc.1 fastMc.2 (fun i hi => by interval_cases i <;> simp only [s0, s1, s2] <;> decide)
      fun i hi h hh => schC_pt (c := 3) (by norm_num) hi hh) (by rw [s0, s1, s2]; rfl)

theorem lc_ok : localChainOK (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs)
    Data.LcommChain = true := by
  obtain ⟨-, -, -, s0, s1, s2⟩ := sizes4
  refine chain_ok (m := 3) (s := 6) (F := lcF) (FI := lcFI) (LEN := lcLEN) (IDX := lcIDX)
    (Mr := lcMr) (PTS := lcPTS) (POS := lcPOS) (PAR := lcPAR) (LAB := lcLAB)
    lcOrig_get.1 (by norm_num) rfl rfl lcStrong_get
    (fun j hj => by rw [lcOrig_get.2 j hj, (lc_lo hj).1]) lcF_pair lc_words
    (fun i hi => (heads4 hi).2.1) (fun i hi => (heads4 hi).2.2.2.2) (fun i hi => ptLc_all hi)
    (fun i hi z hz => (posC4 hi z hz).2)
    (sch_from fastLc.1 fastLc.2 (fun i hi => by interval_cases i <;> simp only [s0, s1, s2] <;> decide)
      fun i hi h hh => schC_pt (c := 4) (by norm_num) hi hh) (by rw [s0, s1, s2]; rfl)

theorem tree_all {i : Nat} (hi : i < 3) : ∀ k < jT i, treePt 245520 (Nat.mul 2 (jLEN i))
    (stepX jF jFI (jIDX i) (jLEN i)) (jPTS i) (jPOS i) (jPAR i) (jLAB i) (bB i) k = true := by
  intro k hk
  have hT : jT i = nat3 245520 52136 36 i := rfl
  interval_cases i
  · have hk' : k < 245520 := hk
    have hs : k / 2048 < 120 := by omega
    have h0 : treeS 0 (k / 2048) = true := tree0All (k / 2048) hs
    unfold treeS at h0
    have h := allN_spec h0 (k % 2048) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul (k / 2048) 2048) (k % 2048) = k := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [e, strictB_eq'', blt_of hk] at h
    exact h
  · have hk' : k < 52136 := hk
    have hs : k / 2048 < 26 := by omega
    have h0 : treeS 1 (k / 2048) = true := tree1All (k / 2048) hs
    unfold treeS at h0
    have h := allN_spec h0 (k % 2048) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul (k / 2048) 2048) (k % 2048) = k := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [e, strictB_eq'', blt_of hk] at h
    exact h
  · have hk' : k < 36 := hk
    exact tree2All k hk'

section

theorem joint_ok : localChainOK jointArrs Data.jointChain = true := by
  have hS := jStrong_get
  have hO : ∀ j < 6, jointArrs[j]! = Array.ofFn (n := 245520) fun i => jF j i.val :=
    fun j hj => by rw [jOrig_get.2 j hj, (j_lo hj).1]
  obtain ⟨hb1, hb2⟩ := base3 Data.jointChain.base rfl
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 6 =>
      CFSG.Monster.B.Co2.permOfArr 245520
        (extendStrong nPts jointArrs Data.jointChain.strongWords)[j.val]!)) ≤ jT 0 * jT 1 * jT 2 := by
    have e : (fun j : Fin 6 => CFSG.Monster.B.Co2.permOfArr 245520
        (extendStrong nPts jointArrs Data.jointChain.strongWords)[j.val]!) =
        fun j => CFSG.Monster.B.Co2.permOfArr 245520 jointArrs[j.val]! := by
      funext j
      rw [hS.2 _ (by omega), hO _ j.isLt]
    rw [e]
    exact joint_card_le
  obtain ⟨pc, sz⟩ := pointChainTree_sound (n := 245520) (m := 6) (s := 9) (chunks := 4)
    (F := jF) (FI := jFI) (B := bB) (LEN := jLEN) (t := jT) (IDX := jIDX) (PTS := jPTS)
    (POS := jPOS) (PAR := jPAR) (LAB := jLAB) hS.1 rfl (by norm_num) (strong_facts hS jF_pair)
    j_words hb1 hb2 (fun i hi => (heads4 hi).2.2.1) (fun i hi => tree_all hi) hcard
  exact local_of hS (by rw [jOrig_get.1]; norm_num) (fun j hj => hO j (by rw [jOrig_get.1] at hj; exact hj))
    (by rw [jOrig_get.1]; exact pc) (sz.trans rfl)

theorem seeds_ok : allBelowN 3 (fun j => pisInv nPts (wordArrs Data.MWords)[j]!
      (pinvCand nPts (wordArrs Data.MWords)[j]!)) = true ∧
    allBelowN 2 (fun j => pisInv nPts (wordArrs Data.LWords)[j]!
      (pinvCand nPts (wordArrs Data.LWords)[j]!)) = true ∧
    pisInv nPts (wordArr Data.pairConjugatorWord)
      (pinvCand nPts (wordArr Data.pairConjugatorWord)) = true := by
  refine ⟨allBelowN_iff.2 fun j hj => ?_, allBelowN_iff.2 fun j hj => ?_, ?_⟩
  · obtain ⟨-, hg, hi⟩ := mW_arr hj
    unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    have p := mG_pair j hj x hx
    rw [hg x hx, hi _ p.1, p.2.2.1]
    simp [p.1]
  · obtain ⟨-, hg, hi⟩ := lW_arr hj
    unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    have p := lG_pair j hj x hx
    rw [hg x hx, hi _ p.1, p.2.2.1]
    simp [p.1]
  · have hc : cArr = wordArr Data.pairConjugatorWord := rfl
    rw [← hc]
    unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    have p := c_pair x hx
    rw [(c_get x hx).1, (ci_get _ p.1).1, p.2.2.1]
    simp [p.1]

theorem facts2213 : (localChainOK (wordArrs Data.TWords) Data.TChain = true)
    ∧ (localChainOK (wordArrs Data.MWords) Data.MChain = true)
    ∧ (localChainOK (wordArrs Data.LWords) Data.LChain = true)
    ∧ (localChainOK (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs) Data.McommChain =
      true)
    ∧ (localChainOK (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs) Data.LcommChain =
      true)
    ∧ (localChainOK jointArrs Data.jointChain = true)
    ∧ (allBelowN 3 (fun j => pisInv nPts (wordArrs Data.MWords)[j]!
        (pinvCand nPts (wordArrs Data.MWords)[j]!)) = true ∧
      allBelowN 2 (fun j => pisInv nPts (wordArrs Data.LWords)[j]!
        (pinvCand nPts (wordArrs Data.LWords)[j]!)) = true ∧
      pisInv nPts (wordArr Data.pairConjugatorWord)
        (pinvCand nPts (wordArr Data.pairConjugatorWord)) = true) :=
  ⟨t_ok, m_ok, l_ok, mc_ok, lc_ok, joint_ok, seeds_ok⟩

end

end CertificateChecks.KernelSpor.ON4K

end
