
module

public import Certificates.Kernel.Sporadic.OddCore.J2CnE
public import Certificates.Kernel.Sporadic.OddCore.J2CnE2
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Sporadic.OddCore.J2LocF
public import CFSG.Certificates.Kernel.J2CoverSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Cn

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem base : szOK 315 9 = true ∧ canonK 315 9 (mask 9) (315 * 9) idK = true ∧
    CFSG.KS.Prim.idK 315 9 (mask 9) = true ∧
    allN 42 (fun k => bAnd(canonK 315 9 (mask 9) (315 * 9) (F k),
      canonK 315 9 (mask 9) (315 * 9) (I k))) = true ∧
    allN 2 (fun j => bAnd(canonK 315 9 (mask 9) (315 * 9) (J2P.S j),
      canonK 315 9 (mask 9) (315 * 9) (J2P.SI j))) = true := by
  simpa only [bAnd_iff] using k_base

theorem hn : szOK 315 9 = true := base.1

theorem hidc : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := base.2.1

theorem hidA : idA 315 = unpack 315 9 (pidn 315 9) := (idK_sound base.2.2.1).symm

theorem hid : idT 315 = tabT (unpack 315 9 (pidn 315 9)) := by rw [idT_tabT, hidA]

theorem Fc {k : Nat} (hk : k < 42) : canonK 315 9 (mask 9) (315 * 9) (F k) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).1

theorem Ic {k : Nat} (hk : k < 42) : canonK 315 9 (mask 9) (315 * 9) (I k) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.1 k hk)).2

theorem Sc {j : Nat} (hj : j < 2) : canonK 315 9 (mask 9) (315 * 9) (J2P.S j) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2 j hj)).1

theorem SIc {j : Nat} (hj : j < 2) : canonK 315 9 (mask 9) (315 * 9) (J2P.SI j) = true :=
  ((bAnd_iff _ _).1 (allN_spec base.2.2.2.2 j hj)).2

theorem Finv {k : Nat} (hk : k < 42) : invEqK 315 9 (mask 9) (315 * 9) (F k) (I k) = true :=
  allN_spec OddCore.j2_perms k hk

theorem tabF {k : Nat} (hk : k < 42) : j2CentTbl k = tabT (unpack 315 9 (F k)) := by
  change j2CentTbl k = tabT (unpack 315 9 (J2CentT.F k))
  rw [← OddCore.j2CentTbl_eq hk, tabT_natArr]

theorem invF {k : Nat} (hk : k < 42) : invT 315 (j2CentTbl k) = tabT (unpack 315 9 (I k)) := by
  rw [tabF hk, invT_unpack (by norm_num) (Finv hk)]

theorem permF {k : Nat} (hk : k < 42) : permOK 315 (j2CentTbl k) = true := by
  rw [tabF hk]
  exact permOK_unpack (Fc hk) (Finv hk)

theorem invOKF {k : Nat} (hk : k < 42) : invOK 315 (j2CentTbl k) (invT 315 (j2CentTbl k)) = true :=
    by
  rw [invF hk, tabF hk]
  exact invOK_unpack (Fc hk) (Ic hk) (Finv hk)

theorem sift_eq {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) :
    j2Sift (tabT (unpack 315 9 X)) = sK X := by
  unfold j2Sift
  rw [natArr_tabT hX]
  obtain ⟨-, -, h2, h3⟩ := CFSG.KS.PF.canon_facts hX
  exact CFSG.KS.Raw.siftK_eq J2PC.bindsP J2PC.permP J2P.hl rfl h2
    (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi))

theorem involF {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) :
    involOK 315 (tabT (unpack 315 9 X)) = involK X := by
  rw [involOK_unpack' (by norm_num) hid hidc hX]
  rfl

theorem pows (X : Nat) : Pows 315 9 X (fun e => pw e X) := by
  refine ⟨rfl, fun e => ?_⟩
  change strictN (pw e X) (fun a => pc X a) = _
  rw [strictN_app']
  rfl

theorem canonP {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) (e : Nat) :
    canonK 315 9 (mask 9) (315 * 9) (pw e X) = true := pows_canon (pows X) hidc hX e

theorem compF {p q : Nat} (hp : canonK 315 9 (mask 9) (315 * 9) p = true)
    (hq : canonK 315 9 (mask 9) (315 * 9) q = true) :
    canonK 315 9 (mask 9) (315 * 9) (pcomp 315 9 (mask 9) p q) = true := canonK_pcomp hp hq

theorem commF {p q : Nat} (hp : canonK 315 9 (mask 9) (315 * 9) p = true)
    (hq : canonK 315 9 (mask 9) (315 * 9) q = true) :
    commTT 315 (tabT (unpack 315 9 p)) (tabT (unpack 315 9 q)) = commK p q := by
  rw [commTT_unpack hp hq]
  rfl

theorem ordF {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) (m : Nat) :
    ordTest 315 m (tabT (unpack 315 9 X)) =
      (isId m X && (divParts m).all fun e => notId e X) := by
  rw [ordTest_unpack (pows X) hidA hidc hX]
  congr 1

theorem selF {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) (p₁ p₂ : Nat) :
    selOK 315 [p₁, p₂] (tabT (unpack 315 9 X)) = selK p₁ p₂ X := by
  rw [selOK_unpack (pows X) hid hidc hX]
  unfold selK isId idK
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  cases Nat.beq X (pidn 315 9) <;> cases Nat.beq (pw p₁ X) (pidn 315 9) <;>
    cases Nat.beq (pw p₂ X) (pidn 315 9) <;> rfl

theorem pg_tabs : TabsOK 315 9 2 J2P.S j2PGTbls := by
  refine ⟨rfl, fun j hj => ⟨?_, Sc hj⟩⟩
  have hb := J2PC.bindsP.2.2.2.2.1 j (by omega)
  interval_cases j
  · change tabT ((CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[0]!) = _
    rw [hb]
  · change tabT ((CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[1]!) = _
    rw [hb]

theorem pgi_tabs : TabsOK 315 9 2 J2P.SI j2PGInvTbls :=
  TabsOK_inv pg_tabs fun j hj => ⟨allN_spec J2PC.permP j (by omega), SIc hj⟩

theorem tabs_range (a k : Nat) (hk : a + k ≤ 42) :
    TabsOK 315 9 k (fun j => F (Nat.add a j))
      ((List.range k).map fun j => j2CentTbl (a + j)).toArray := by
  refine ⟨by simp, fun j hj => ⟨?_, Fc (by change a + j < 42; omega)⟩⟩
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  exact tabF (by omega)

theorem invs_range (a k : Nat) (hk : a + k ≤ 42) :
    ∀ j < k, invEqK 315 9 (mask 9) (315 * 9) (F (Nat.add a j)) (I (Nat.add a j)) = true ∧
      canonK 315 9 (mask 9) (315 * 9) (I (Nat.add a j)) = true :=
  fun j hj => ⟨Finv (by change a + j < 42; omega), Ic (by change a + j < 42; omega)⟩

theorem itabs_range (a k : Nat) (hk : a + k ≤ 42) :
    TabsOK 315 9 k (fun j => I (Nat.add a j))
      (((List.range k).map fun j => j2CentTbl (a + j)).toArray.map (invT 315)) :=
  TabsOK_inv (tabs_range a k hk) (invs_range a k hk)

theorem eq_of {G G' : Nat → Nat} {k : Nat} (h : allN k (fun j => Nat.beq (G' j) (G j)) = true) :
    ∀ j < k, G' j = G j := fun j hj => Nat.eq_of_beq_eq_true (allN_spec h j hj)

theorem bindO : (allN 2 (fun j => bAnd(Nat.beq (J2R1.G j) (J2P.S j), Nat.beq (J2R1.GI j) (J2P.SI
    j))) =
      true ∧
    allN 2 (fun j => bAnd(Nat.beq (J2R2.G j) (J2P.S j), Nat.beq (J2R2.GI j) (J2P.SI j))) = true ∧
    allN 2 (fun j => bAnd(Nat.beq (J2R3.G j) (J2P.S j), Nat.beq (J2R3.GI j) (J2P.SI j))) = true) ∧
    Nat.beq J2R1.R (F 9) = true ∧ Nat.beq J2R2.R (F 17) = true ∧ Nat.beq J2R3.R (F 31) = true := by
  have h := k_bindO
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, b1, b2, b3⟩ := h
  exact ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩

theorem pair_of {k : Nat} {G GI S SI : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (G j) (S j), Nat.beq (GI j) (SI j))) = true) :
    (∀ j < k, G j = S j) ∧ ∀ j < k, GI j = SI j :=
  ⟨fun j hj => Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).1,
    fun j hj => Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).2⟩

theorem pe_all' {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, penumPtK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => penumSl_spec h i (Nat.zero_le _) (by omega) hi

theorem sl_all' {cnt : Nat} {P : Nat → Bool} (h : slK cnt P 0 cnt = true) :
    ∀ c < cnt, P c = true :=
  fun c hc => slK_spec h c (Nat.zero_le _) (by omega) hc

theorem heads : penumHdK J2R1.R J2R1.cnt 3000 J2R1.T J2R1.PL = true ∧
    penumHdK J2R2.R J2R2.cnt 3000 J2R2.T J2R2.PL = true ∧
    penumHdK J2R3.R J2R3.cnt 3000 J2R3.T J2R3.PL = true ∧
    penumHdK idK J2SY.cnt 3000 J2SY.T J2SY.PL = true ∧ penumHdK idK J2K1.cnt 3000 J2K1.T J2K1.PL =
        true ∧
    penumHdK J2Q1a.R J2Q1a.cnt 3000 J2Q1a.T J2Q1a.PL = true ∧
    penumHdK J2Q1b.R J2Q1b.cnt 3000 J2Q1b.T J2Q1b.PL = true ∧
    penumHdK J2Q2a.R J2Q2a.cnt 3000 J2Q2a.T J2Q2a.PL = true ∧
    penumHdK J2Q2b.R J2Q2b.cnt 3000 J2Q2b.T J2Q2b.PL = true ∧
    penumHdK J2Q2c.R J2Q2c.cnt 3000 J2Q2c.T J2Q2c.PL = true ∧
    penumHdK J2Q3a.R J2Q3a.cnt 3000 J2Q3a.T J2Q3a.PL = true ∧
    penumHdK J2Q3b.R J2Q3b.cnt 3000 J2Q3b.T J2Q3b.PL = true ∧
    penumHdK J2Q3c.R J2Q3c.cnt 3000 J2Q3c.T J2Q3c.PL = true ∧
    penumHdK idK J2E2a.cnt 3000 J2E2a.T J2E2a.PL = true ∧
    penumHdK idK J2E2b.cnt 3000 J2E2b.T J2E2b.PL = true ∧
    penumHdK idK J2C1.cnt 3000 J2C1.T J2C1.PL = true ∧
    penumHdK idK J2C2.cnt 3000 J2C2.T J2C2.PL = true := by
  simpa only [bAnd_iff] using k_heads

theorem cover {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem sizes : J2R1.cnt = 1800 ∧ J2R2.cnt = 2520 ∧ J2R3.cnt = 315 ∧ J2SY.cnt = 256 ∧
    J2K1.cnt = 336 ∧ J2Q1a.cnt = 48 ∧ J2Q1b.cnt = 56 ∧ J2Q2a.cnt = 12 ∧ J2Q2b.cnt = 12 ∧
    J2Q2c.cnt = 20 ∧ J2Q3a.cnt = 80 ∧ J2Q3b.cnt = 192 ∧ J2Q3c.cnt = 192 ∧ J2E2a.cnt = 60 ∧
    J2E2b.cnt = 60 := by
  have h := k_sizes
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact h

theorem r1_pe : ∀ i < J2R1.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2R1.G J2R1.GI 2 J2R1.cnt
    J2R1.T J2R1.PL J2R1.POS J2R1.SRT J2R1.SRI i = true := by
  have hc : J2R1.cnt = 450 * 4 := by rw [sizes.1]
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2R1.cnt := by rw [hc]; omega
  interval_cases s
  · exact penumSl_spec o1E0 i h1 h2 hi
  · exact penumSl_spec o1E1 i h1 h2 hi
  · exact penumSl_spec o1E2 i h1 h2 hi
  · exact penumSl_spec o1E3 i h1 h2 hi

theorem r1_hs : ∀ i < J2R1.cnt, hsortPtK 315 9 (mask 9) J2R1.cnt J2R1.T J2R1.HS J2R1.HSI i = true
    := by
  have hc : J2R1.cnt = 900 * 2 := by rw [sizes.1]
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2R1.cnt := by rw [hc]; omega
  interval_cases s
  · exact slK_spec o1H0 i h1 h2 hi
  · exact slK_spec o1H1 i h1 h2 hi

theorem r2_pe : ∀ i < J2R2.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2R2.G J2R2.GI 2 J2R2.cnt
    J2R2.T J2R2.PL J2R2.POS J2R2.SRT J2R2.SRI i = true := by
  have hc : J2R2.cnt = 420 * 6 := by rw [sizes.2.1]
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2R2.cnt := by rw [hc]; omega
  interval_cases s
  · exact penumSl_spec o2E0 i h1 h2 hi
  · exact penumSl_spec o2E1 i h1 h2 hi
  · exact penumSl_spec o2E2 i h1 h2 hi
  · exact penumSl_spec o2E3 i h1 h2 hi
  · exact penumSl_spec o2E4 i h1 h2 hi
  · exact penumSl_spec o2E5 i h1 h2 hi

theorem r2_hs : ∀ i < J2R2.cnt, hsortPtK 315 9 (mask 9) J2R2.cnt J2R2.T J2R2.HS J2R2.HSI i = true
    := by
  have hc : J2R2.cnt = 840 * 3 := by rw [sizes.2.1]
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2R2.cnt := by rw [hc]; omega
  interval_cases s
  · exact slK_spec o2H0 i h1 h2 hi
  · exact slK_spec o2H1 i h1 h2 hi
  · exact slK_spec o2H2 i h1 h2 hi

@[expose] def cgL (a k : Nat) : List Table := (List.range k).map fun j => j2CentTbl (a + j)

theorem cg_tabs (a k : Nat) (hk : a + k ≤ 42) : TabsOK 315 9 k (fun j => F (Nat.add a j)) (cgL a
    k).toArray :=
  tabs_range a k hk

theorem cgi_tabs (a k : Nat) (hk : a + k ≤ 42) :
    TabsOK 315 9 k (fun j => I (Nat.add a j)) ((cgL a k).toArray.map (invT 315)) :=
  itabs_range a k hk

theorem sy_eq : j2SylowGenTbls = cgL 1 8 := by
  unfold j2SylowGenTbls cgL
  apply List.map_congr_left
  intro i _
  rw [Nat.add_comm]

theorem bindM : (allN 8 (fun j => bAnd(Nat.beq (J2SY.G j) idK, Nat.beq (J2SY.GI j) (F (Nat.succ
    j)))) =
      true ∧
    allN 3 (fun j => bAnd(Nat.beq (J2K1.G j) idK, Nat.beq (J2K1.GI j) (F (Nat.add 10 j)))) = true) ∧
    allN 2 (fun j => bAnd(Nat.beq (J2E2a.G j) idK, Nat.beq (J2E2a.GI j) (F (Nat.add 24 j)))) = true
        ∧
    allN 2 (fun j => bAnd(Nat.beq (J2E2b.G j) idK, Nat.beq (J2E2b.GI j) (F (Nat.add 27 j)))) = true
        := by
  have h := k_bindM
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4⟩ := h
  exact ⟨⟨a1, a2⟩, a3, a4⟩

theorem recSY : mulClosureH 315 (cgL 1 8).toArray 3000 = hRec 315 9 J2SY.cnt J2SY.T J2SY.PL ∧
    mulTreeOK 315 (cgL 1 8).toArray (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).1
      (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).2.1 (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of (S := fun _ => idK) (SI := (fun j => F (Nat.succ j))) bindM.1.1
  have hGI' : ∀ j < 8, J2SY.GI j = F (Nat.add 1 j) := fun j hj => by
    rw [hGI j hj]
    congr 1
    change j + 1 = 1 + j
    omega
  exact mulH_sound hn hG (TabsOK_congr hGI' (cg_tabs 1 8 (by norm_num))) heads.2.2.2.1 (pe_all' syE)
    (sl_all' syH)

theorem recK1 : mulClosureH 315 (cgL 10 3).toArray 3000 = hRec 315 9 J2K1.cnt J2K1.T J2K1.PL ∧
    mulTreeOK 315 (cgL 10 3).toArray (hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).1
      (hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).2.1 (hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of (S := fun _ => idK) (SI := (fun j => F (Nat.add 10 j))) bindM.1.2
  exact mulH_sound hn hG (TabsOK_congr hGI (cg_tabs 10 3 (by norm_num))) heads.2.2.2.2.1 (pe_all'
      k1E)
    (sl_all' k1H)

theorem recE2a : mulClosureH 315 (cgL 24 2).toArray 3000 = hRec 315 9 J2E2a.cnt J2E2a.T J2E2a.PL ∧
    mulTreeOK 315 (cgL 24 2).toArray (hRec 315 9 J2E2a.cnt J2E2a.T J2E2a.PL).1
      (hRec 315 9 J2E2a.cnt J2E2a.T J2E2a.PL).2.1 (hRec 315 9 J2E2a.cnt J2E2a.T J2E2a.PL).2.2 =
          true ∧
    hkeysDistinct 315 (hRec 315 9 J2E2a.cnt J2E2a.T J2E2a.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of (S := fun _ => idK) (SI := (fun j => F (Nat.add 24 j))) bindM.2.1
  exact mulH_sound hn hG (TabsOK_congr hGI (cg_tabs 24 2 (by norm_num)))
      heads.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (pe_all' e2aE)
    (sl_all' e2aH)

theorem recE2b : mulClosureH 315 (cgL 27 2).toArray 3000 = hRec 315 9 J2E2b.cnt J2E2b.T J2E2b.PL ∧
    mulTreeOK 315 (cgL 27 2).toArray (hRec 315 9 J2E2b.cnt J2E2b.T J2E2b.PL).1
      (hRec 315 9 J2E2b.cnt J2E2b.T J2E2b.PL).2.1 (hRec 315 9 J2E2b.cnt J2E2b.T J2E2b.PL).2.2 =
          true ∧
    hkeysDistinct 315 (hRec 315 9 J2E2b.cnt J2E2b.T J2E2b.PL).1.toList = true := by
  obtain ⟨hG, hGI⟩ := pair_of (S := fun _ => idK) (SI := (fun j => F (Nat.add 27 j))) bindM.2.2
  exact mulH_sound hn hG (TabsOK_congr hGI (cg_tabs 27 2 (by norm_num)))
      heads.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (pe_all' e2bE)
    (sl_all' e2bH)

theorem recC1 : mulClosureH 315 (cgL 18 5).toArray 3000 = hRec 315 9 J2C1.cnt J2C1.T J2C1.PL ∧
    mulTreeOK 315 (cgL 18 5).toArray (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1
      (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).2.1 (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1.toList = true := by
  have hGI : ∀ j < 5, J2C1.GI j = F (Nat.add 18 j) := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (allN_spec J2Loc.gens.1.2.2.1 j hj)]
    unfold J2Loc.c1L F
    congr 1
    change 17 + (j + 1) = 18 + j
    omega
  exact mulH_sound hn (J2Loc.ids_of J2Loc.idv.1.2.1) (TabsOK_congr hGI (cg_tabs 18 5 (by
      norm_num))) heads.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (J2Loc.pe_all J2Loc.c1E) (J2Loc.sl_all J2Loc.c1H)

theorem recC2 : mulClosureH 315 (cgL 32 4).toArray 3000 = hRec 315 9 J2C2.cnt J2C2.T J2C2.PL ∧
    mulTreeOK 315 (cgL 32 4).toArray (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1
      (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).2.1 (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1.toList = true := by
  have hGI : ∀ j < 4, J2C2.GI j = F (Nat.add 32 j) := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (allN_spec J2Loc.gens.1.2.2.2.1 j hj)]
    unfold J2Loc.c2L F
    congr 1
    change 31 + (j + 1) = 32 + j
    omega
  exact mulH_sound hn (J2Loc.ids_of J2Loc.idv.1.2.2.2) (TabsOK_congr hGI (cg_tabs 32 4 (by
      norm_num))) heads.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    J2Loc.c2_pe J2Loc.c2_hs

theorem rbind {G GI : Nat → Nat} (h : allN 2 (fun j => bAnd(Nat.beq (G j) (J2P.S j),
    Nat.beq (GI j) (J2P.SI j))) = true) :
    TabsOK 315 9 2 G j2PGTbls ∧ TabsOK 315 9 2 GI j2PGInvTbls :=
  ⟨TabsOK_congr (pair_of h).1 pg_tabs, TabsOK_congr (pair_of h).2 pgi_tabs⟩

theorem recR1 : conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 9) 3000 = hRec 315 9 J2R1.cnt
    J2R1.T J2R1.PL ∧
    conjTreeOK 315 j2PGTbls j2PGInvTbls (j2CentTbl 9) (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).1
      (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).2.1 (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).1.toList = true :=
  conjH_sound hn (rbind bindO.1.1).1 (rbind bindO.1.1).2
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindO.2.1]) heads.1 r1_pe r1_hs

theorem recR2 : conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 17) 3000 = hRec 315 9 J2R2.cnt
    J2R2.T J2R2.PL ∧
    conjTreeOK 315 j2PGTbls j2PGInvTbls (j2CentTbl 17) (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).1
      (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).2.1 (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).1.toList = true :=
  conjH_sound hn (rbind bindO.1.2.1).1 (rbind bindO.1.2.1).2
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindO.2.2.1]) heads.2.1 r2_pe r2_hs

theorem recR3 : conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 31) 3000 = hRec 315 9 J2R3.cnt
    J2R3.T J2R3.PL ∧
    conjTreeOK 315 j2PGTbls j2PGInvTbls (j2CentTbl 31) (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).1
      (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).2.1 (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).1.toList = true :=
  conjH_sound hn (rbind bindO.1.2.2).1 (rbind bindO.1.2.2).2
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindO.2.2.2]) heads.2.2.1 (pe_all' o3E)
        (sl_all' o3H)

theorem bindQ : (allN 3 (fun j => bAnd(Nat.beq (J2Q1a.G j) (F (Nat.add 10 j)),
      bAnd(Nat.beq (J2Q1a.GI j) (I (Nat.add 10 j)), bAnd(Nat.beq (J2Q1b.G j) (F (Nat.add 10 j)),
      Nat.beq (J2Q1b.GI j) (I (Nat.add 10 j)))))) = true) ∧
    (allN 5 (fun j => bAnd(Nat.beq (J2Q2a.G j) (F (Nat.add 18 j)),
      bAnd(Nat.beq (J2Q2a.GI j) (I (Nat.add 18 j)), bAnd(Nat.beq (J2Q2b.G j) (F (Nat.add 18 j)),
      bAnd(Nat.beq (J2Q2b.GI j) (I (Nat.add 18 j)), bAnd(Nat.beq (J2Q2c.G j) (F (Nat.add 18 j)),
      Nat.beq (J2Q2c.GI j) (I (Nat.add 18 j)))))))) = true) ∧
    (allN 4 (fun j => bAnd(Nat.beq (J2Q3a.G j) (F (Nat.add 32 j)),
      bAnd(Nat.beq (J2Q3a.GI j) (I (Nat.add 32 j)), bAnd(Nat.beq (J2Q3b.G j) (F (Nat.add 32 j)),
      bAnd(Nat.beq (J2Q3b.GI j) (I (Nat.add 32 j)), bAnd(Nat.beq (J2Q3c.G j) (F (Nat.add 32 j)),
      Nat.beq (J2Q3c.GI j) (I (Nat.add 32 j)))))))) = true) ∧
    Nat.beq J2Q1a.R (F 13) = true ∧ Nat.beq J2Q1b.R (F 15) = true ∧ Nat.beq J2Q2a.R (F 23) = true ∧
    Nat.beq J2Q2b.R (F 26) = true ∧ Nat.beq J2Q2c.R (F 29) = true ∧ Nat.beq J2Q3a.R (F 36) = true ∧
    Nat.beq J2Q3b.R (F 38) = true ∧ Nat.beq J2Q3c.R (F 40) = true := by
  have h := k_bindQ
  simp only [bAnd_iff] at h
  obtain ⟨a, b, c, r1, r2, r3, r4, r5, r6, r7, r8⟩ := h
  exact ⟨a, b, c, r1, r2, r3, r4, r5, r6, r7, r8⟩

theorem qeq {k : Nat} {f : Nat → Bool} (h : allN k f = true) : ∀ j < k, f j = true :=
  fun j hj => allN_spec h j hj

theorem recQ1a : conjClosureH 315 (cgL 10 3).toArray ((cgL 10 3).toArray.map (invT 315))
      (j2CentTbl 13) 3000 = hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL ∧
    conjTreeOK 315 (cgL 10 3).toArray ((cgL 10 3).toArray.map (invT 315)) (j2CentTbl 13)
      (hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL).1 (hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL).2.1
      (hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL).1.toList = true := by
  have hb : ∀ j < 3, J2Q1a.G j = F (Nat.add 10 j) ∧ J2Q1a.GI j = I (Nat.add 10 j) := by
    intro j hj
    have h := qeq bindQ.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1,
      Nat.eq_of_beq_eq_true h.2.1⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 10 3 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 10 3 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.1]) heads.2.2.2.2.2.1 (pe_all'
        q1aE)
    (sl_all' q1aH)

theorem recQ1b : conjClosureH 315 (cgL 10 3).toArray ((cgL 10 3).toArray.map (invT 315))
      (j2CentTbl 15) 3000 = hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL ∧
    conjTreeOK 315 (cgL 10 3).toArray ((cgL 10 3).toArray.map (invT 315)) (j2CentTbl 15)
      (hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL).1 (hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL).2.1
      (hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL).1.toList = true := by
  have hb : ∀ j < 3, J2Q1b.G j = F (Nat.add 10 j) ∧ J2Q1b.GI j = I (Nat.add 10 j) := by
    intro j hj
    have h := qeq bindQ.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.2.2.1,
      Nat.eq_of_beq_eq_true h.2.2.2⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 10 3 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 10 3 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.1]) heads.2.2.2.2.2.2.1
        (pe_all' q1bE)
    (sl_all' q1bH)

theorem recQ2a : conjClosureH 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315))
      (j2CentTbl 23) 3000 = hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL ∧
    conjTreeOK 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315)) (j2CentTbl 23)
      (hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL).1 (hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL).2.1
      (hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL).1.toList = true := by
  have hb : ∀ j < 5, J2Q2a.G j = F (Nat.add 18 j) ∧ J2Q2a.GI j = I (Nat.add 18 j) := by
    intro j hj
    have h := qeq bindQ.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1,
      Nat.eq_of_beq_eq_true h.2.1⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 18 5 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 18 5 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.1]) heads.2.2.2.2.2.2.2.1
        (pe_all' q2aE)
    (sl_all' q2aH)

theorem recQ2b : conjClosureH 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315))
      (j2CentTbl 26) 3000 = hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL ∧
    conjTreeOK 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315)) (j2CentTbl 26)
      (hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL).1 (hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL).2.1
      (hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL).1.toList = true := by
  have hb : ∀ j < 5, J2Q2b.G j = F (Nat.add 18 j) ∧ J2Q2b.GI j = I (Nat.add 18 j) := by
    intro j hj
    have h := qeq bindQ.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.2.2.1,
      Nat.eq_of_beq_eq_true h.2.2.2.1⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 18 5 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 18 5 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.2.1]) heads.2.2.2.2.2.2.2.2.1
        (pe_all' q2bE)
    (sl_all' q2bH)

theorem recQ2c : conjClosureH 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315))
      (j2CentTbl 29) 3000 = hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL ∧
    conjTreeOK 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315)) (j2CentTbl 29)
      (hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL).1 (hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL).2.1
      (hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL).1.toList = true := by
  have hb : ∀ j < 5, J2Q2c.G j = F (Nat.add 18 j) ∧ J2Q2c.GI j = I (Nat.add 18 j) := by
    intro j hj
    have h := qeq bindQ.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.2.2.2.2.1,
      Nat.eq_of_beq_eq_true h.2.2.2.2.2⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 18 5 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 18 5 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.2.2.1])
        heads.2.2.2.2.2.2.2.2.2.1 (pe_all' q2cE)
    (sl_all' q2cH)

theorem recQ3a : conjClosureH 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315))
      (j2CentTbl 36) 3000 = hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL ∧
    conjTreeOK 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315)) (j2CentTbl 36)
      (hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL).1 (hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL).2.1
      (hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL).1.toList = true := by
  have hb : ∀ j < 4, J2Q3a.G j = F (Nat.add 32 j) ∧ J2Q3a.GI j = I (Nat.add 32 j) := by
    intro j hj
    have h := qeq bindQ.2.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1,
      Nat.eq_of_beq_eq_true h.2.1⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 32 4 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 32 4 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.2.2.2.1])
        heads.2.2.2.2.2.2.2.2.2.2.1 (pe_all' q3aE)
    (sl_all' q3aH)

theorem recQ3b : conjClosureH 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315))
      (j2CentTbl 38) 3000 = hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL ∧
    conjTreeOK 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315)) (j2CentTbl 38)
      (hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL).1 (hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL).2.1
      (hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL).1.toList = true := by
  have hb : ∀ j < 4, J2Q3b.G j = F (Nat.add 32 j) ∧ J2Q3b.GI j = I (Nat.add 32 j) := by
    intro j hj
    have h := qeq bindQ.2.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.2.2.1,
      Nat.eq_of_beq_eq_true h.2.2.2.1⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 32 4 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 32 4 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.2.2.2.2.1])
        heads.2.2.2.2.2.2.2.2.2.2.2.1 (pe_all' q3bE)
    (sl_all' q3bH)

theorem recQ3c : conjClosureH 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315))
      (j2CentTbl 40) 3000 = hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL ∧
    conjTreeOK 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315)) (j2CentTbl 40)
      (hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL).1 (hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL).2.1
      (hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL).2.2 = true ∧
    hkeysDistinct 315 (hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL).1.toList = true := by
  have hb : ∀ j < 4, J2Q3c.G j = F (Nat.add 32 j) ∧ J2Q3c.GI j = I (Nat.add 32 j) := by
    intro j hj
    have h := qeq bindQ.2.2.1 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.2.2.2.2.1,
      Nat.eq_of_beq_eq_true h.2.2.2.2.2⟩
  exact conjH_sound hn (TabsOK_congr (fun j hj => (hb j hj).1) (cg_tabs 32 4 (by norm_num)))
    (TabsOK_congr (fun j hj => (hb j hj).2) (cgi_tabs 32 4 (by norm_num)))
    (by rw [tabF (by norm_num), Nat.eq_of_beq_eq_true bindQ.2.2.2.2.2.2.2.2.2.2])
        heads.2.2.2.2.2.2.2.2.2.2.2.2.1 (pe_all' q3cE)
    (sl_all' q3cH)

theorem u_tab : j2OuterTbl = tabT (unpack 315 9 (F 0)) := tabF (by norm_num)

theorem ufacts : involK (F 0) = true ∧ bIf(sK (F 0), false, true) = true ∧
    allN 2 (fun j => bAnd(sK (J2P.S j), sK (pc (pc (F 0) (J2P.S j)) (I 0)))) = true := by
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

theorem sy_tabs' : TabsOK 315 9 8 (fun j => F (Nat.succ j)) (cgL 1 8).toArray :=
  TabsOK_congr (fun j _ => by
    change F (j + 1) = F (1 + j)
    rw [Nat.add_comm]) (cg_tabs 1 8 (by norm_num))

theorem sy_invs : ∀ j < 8, invEqK 315 9 (mask 9) (315 * 9) (F (Nat.succ j)) (I (Nat.succ j)) = true
    ∧
    canonK 315 9 (mask 9) (315 * 9) (I (Nat.succ j)) = true :=
  fun j hj => ⟨Finv (by omega), Ic (by omega)⟩

theorem sy_cl : ∀ c < J2SY.cnt * (8 + 8), findPtK J2SY.cnt J2SY.T
    (prodQK 315 9 (mask 9) (8 + 8) J2SY.T (bothK 8 (fun j => F (Nat.succ j))
      (fun j => I (Nat.succ j)))) J2SYCl c = true := by
  have hc : J2SY.cnt * (8 + 8) = 2048 * 2 := by rw [sizes.2.2.2.1]
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < Nat.mul J2SY.cnt 16 := by
    change i < J2SY.cnt * 16
    rw [sizes.2.2.2.1]
    omega
  interval_cases s
  · exact slK_spec syCl0 i h1 h2 hi
  · exact slK_spec syCl1 i h1 h2 hi

theorem syl_ok : CFSG.Sporadic.SmallOddCore.sylowOK 315 3000 j2PGTbls j2PGInvTbls j2Sift j2OuterTbl
    j2SylowGenTbls
    j2SylowOrder = true := by
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
    rw [← getElem!_pos j2PGTbls j hj, (pg_tabs.2 j hj').1, sift_eq (Sc hj')]
    exact ((bAnd_iff _ _).1 (allN_spec hu3 j hj')).1
  · simp [j2PGInvTbls]
  · rw [CFSG.KS.TW.allIn_iff]
    intro l hl
    have hl' : l < 2 := by rw [← pg_tabs.1]; exact hl
    rw [(pg_tabs.2 l hl').1, (pgi_tabs.2 l hl').1]
    exact invOK_unpack (Sc hl') (SIc hl') (allN_spec J2PC.permP l (by omega))
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 2 := by rw [← pg_tabs.1]; exact hj
    rw [← getElem!_pos j2PGTbls j hj, (pg_tabs.2 j hj').1, u_tab, invT_unpack (by norm_num) (Finv (by norm_num)),
      conjT_unpack (Fc (by norm_num)) (Ic (by norm_num)) (Sc hj'),
      sift_eq (compF (compF (Fc (by norm_num)) (Sc hj')) (Ic (by norm_num)))]
    exact ((bAnd_iff _ _).1 (allN_spec hu3 j hj')).2
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 8 := by rw [← sy_tabs'.1]; exact hj
    obtain ⟨hg, hc⟩ := sy_tabs'.2 j hj'
    dsimp only at hg hc
    rw [← getElem!_pos _ j hj, hg, invT_unpack (by norm_num) (sy_invs j hj').1, u_tab]
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack hc (sy_invs j hj').1, invOK_unpack hc (sy_invs j hj').2 (sy_invs j
        hj').1⟩,
      ?_⟩
    rw [compT_unpack hc (Fc (by norm_num)), sift_eq hc, sift_eq (compF hc (Fc (by norm_num)))]
    exact orB (allN_spec k_syl j hj')
  · exact closedOK_of (fun i hi => penumPt_canon (pe_all' syE i hi))
      (TabsOK_both sy_tabs' sy_invs) sy_cl
  · rw [hRec_size, sizes.2.2.2.1]
    rfl

theorem kodd : oddK 13 7 9 = true ∧ oddK 15 3 9 = true ∧ oddK 23 5 17 = true ∧ oddK 26 5 17 = true ∧
    oddK 29 3 17 = true ∧ oddK 36 3 31 = true ∧ oddK 38 5 31 = true ∧ oddK 40 5 31 = true := by
  simpa only [bAnd_iff] using k_odd

theorem kconj : conjK 14 9 = true ∧ conjK 16 9 = true ∧ conjK 30 17 = true ∧ conjK 37 31 = true ∧
    conjK 39 31 = true ∧ conjK 41 31 = true := by
  simpa only [bAnd_iff] using k_conj

theorem kreps : involK (F 9) = true ∧ involK (F 17) = true ∧ involK (F 31) = true ∧
    bIf(sK (F 9), false, true) = true ∧ sK (pc (F 9) (F 0)) = true ∧ sK (F 17) = true ∧
    sK (F 31) = true := by
  simpa only [bAnd_iff] using k_reps

theorem kcg : allN 3 (fun j => bAnd(sK (F (Nat.add 10 j)), commK (F (Nat.add 10 j)) (F 9))) = true ∧
    allN 5 (fun j => bAnd(sK (F (Nat.add 18 j)), commK (F (Nat.add 18 j)) (F 17))) = true ∧
    allN 4 (fun j => bAnd(sK (F (Nat.add 32 j)), commK (F (Nat.add 32 j)) (F 31))) = true := by
  simpa only [bAnd_iff] using k_cg

theorem siftF {k : Nat} (hk : k < 42) : j2Sift (j2CentTbl k) = sK (F k) := by
  rw [tabF hk, sift_eq (Fc hk)]

theorem commFF {a b : Nat} (ha : a < 42) (hb : b < 42) :
    commTT 315 (j2CentTbl a) (j2CentTbl b) = commK (F a) (F b) := by
  rw [tabF ha, tabF hb, commF (Fc ha) (Fc hb)]

theorem cg_all (a k t : Nat) (hk : a + k ≤ 42) (ht : t < 42)
    (h : allN k (fun j => bAnd(sK (F (Nat.add a j)), commK (F (Nat.add a j)) (F t))) = true) :
    (cgL a k).toArray.all (fun c => permOK 315 c && j2Sift c && commTT 315 c (j2CentTbl t) &&
      invOK 315 c (invT 315 c)) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < k := by rw [← (cg_tabs a k hk).1]; exact hj
  have hl : Nat.add a j < 42 := by change a + j < 42; omega
  obtain ⟨hg, hc⟩ := (cg_tabs a k hk).2 j hj'
  dsimp only at hg hc
  rw [← getElem!_pos _ j hj, hg, invT_unpack (by norm_num) (Finv hl), tabF ht, sift_eq hc, commF hc (Fc ht)]
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec h j hj')
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨permOK_unpack hc (Finv hl), h1⟩, h2⟩, invOK_unpack hc (Ic hl) (Finv hl)⟩

theorem oddF {r p t : Nat} (hr : r < 42) (ht : t < 42) (h : oddK r p t = true)
    (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1]) :
    permOK 315 (j2CentTbl r) = true ∧ j2Sift (j2CentTbl r) = true ∧
      commTT 315 (j2CentTbl r) (j2CentTbl t) = true ∧
      CFSG.Sporadic.Schreier.Native.ordTest 315 p (j2CentTbl r) = true := by
  unfold oddK at h
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using h :
    sK (F r) = true ∧ commK (F r) (F t) = true ∧ isId p (F r) = true ∧ notId 1 (F r) = true)
  refine ⟨permF hr, by rw [siftF hr]; exact h1, by rw [commFF hr ht]; exact h2, ?_⟩
  rw [tabF hr, ordF (Fc hr), hdp]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h3, h4⟩

theorem odd_conj {r p h t ord cs : Nat} (hr : r < 42) (hh : h < 42) (ht : t < 42)
    (ho : oddK r p t = true) (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1])
    (hc : conjK h t = true)
    (hord : (isId ord (cw (F r) (F h) (I h)) &&
      (CFSG.Sporadic.Schreier.Native.divParts ord).all fun e => notId e (cw (F r) (F h) (I h))) =
        true)
    (h2 : ord % 2 = 0) (h0 : 0 < ord) {cg cgInv : Array Table} :
    oddRowOK 315 3000 j2Sift (j2CentTbl t) cg cgInv
      { rep := j2CentTbl r, prime := p, classSize := cs, wit := .conj (j2CentTbl h) ord } =
        true := by
  obtain ⟨a1, a2, a3, a4⟩ := oddF hr ht ho hdp
  unfold conjK at hc
  obtain ⟨c1, c2⟩ := (bAnd_iff _ _).1 hc
  have b7 : CFSG.Sporadic.Schreier.Native.ordTest 315 ord (compT 315 (j2CentTbl r)
      (conjT 315 (j2CentTbl h) (invT 315 (j2CentTbl h)) (j2CentTbl r))) = true := by
    rw [invF hh, tabF hh, tabF hr, conjT_unpack (Fc hh) (Ic hh) (Fc hr),
      compT_unpack (Fc hr) (compF (compF (Fc hh) (Fc hr)) (Ic hh)),
      ordF (compF (Fc hr) (compF (compF (Fc hh) (Fc hr)) (Ic hh)))]
    exact hord
  unfold oddRowOK
  simp only [a1, a2, a3, a4, permF hh, siftF hh, c1, commFF hh ht, c2, invOKF hh, b7, h2, h0,
    Bool.and_true, beq_self_eq_true, decide_true]

theorem kord : (isId 4 (cw (F 13) (F 14) (I 14)) = true ∧ notId 2 (cw (F 13) (F 14) (I 14)) = true ∧
      notId 1 (cw (F 13) (F 14) (I 14)) = true) ∧
    (isId 4 (cw (F 15) (F 16) (I 16)) = true ∧ notId 2 (cw (F 15) (F 16) (I 16)) = true ∧
      notId 1 (cw (F 15) (F 16) (I 16)) = true) ∧
    (isId 2 (cw (F 29) (F 30) (I 30)) = true ∧ notId 1 (cw (F 29) (F 30) (I 30)) = true) ∧
    (isId 6 (cw (F 36) (F 37) (I 37)) = true ∧ notId 3 (cw (F 36) (F 37) (I 37)) = true ∧
      notId 2 (cw (F 36) (F 37) (I 37)) = true ∧ notId 1 (cw (F 36) (F 37) (I 37)) = true) ∧
    (isId 4 (cw (F 38) (F 39) (I 39)) = true ∧ notId 2 (cw (F 38) (F 39) (I 39)) = true ∧
      notId 1 (cw (F 38) (F 39) (I 39)) = true) ∧
    (isId 4 (cw (F 40) (F 41) (I 41)) = true ∧ notId 2 (cw (F 40) (F 41) (I 41)) = true ∧
      notId 1 (cw (F 40) (F 41) (I 41)) = true) := by
  simpa only [bAnd_iff] using k_ord

theorem ord4 {y : Nat} (h : isId 4 y = true ∧ notId 2 y = true ∧ notId 1 y = true) :
    (isId 4 y && (CFSG.Sporadic.Schreier.Native.divParts 4).all fun e => notId e y) = true := by
  have hd : CFSG.Sporadic.Schreier.Native.divParts 4 = [2, 1] := by decide
  rw [hd]
  simp [h.1, h.2.1, h.2.2]

theorem ord2 {y : Nat} (h : isId 2 y = true ∧ notId 1 y = true) :
    (isId 2 y && (CFSG.Sporadic.Schreier.Native.divParts 2).all fun e => notId e y) = true := by
  have hd : CFSG.Sporadic.Schreier.Native.divParts 2 = [1] := by decide
  rw [hd]
  simp [h.1, h.2]

theorem ord6 {y : Nat}
    (h : isId 6 y = true ∧ notId 3 y = true ∧ notId 2 y = true ∧ notId 1 y = true) :
    (isId 6 y && (CFSG.Sporadic.Schreier.Native.divParts 6).all fun e => notId e y) = true := by
  have hd : CFSG.Sporadic.Schreier.Native.divParts 6 = [3, 2, 1] := by decide
  rw [hd]
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem mem_at {cnt i y : Nat} {T PL POS : Nat → Nat}
    (hT : ∀ q < cnt, canonK 315 9 (mask 9) (315 * 9) (T q) = true)
    (hy : canonK 315 9 (mask 9) (315 * 9) y = true) (h : atK cnt T POS i y = true) :
    memT 315 (hRec 315 9 cnt T PL).1 (tabT (unpack 315 9 y)) = true := by
  unfold atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hq : r32 POS i < cnt := Nat.le_of_ble_eq_true h1
  refine memT_of hq ?_
  rw [tblEq_unpack hy (hT _ hq), ← Nat.eq_of_beq_eq_true h2, Nat.beq_refl]

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < (hRec 315 9 cnt T PL).1.size) :
    (hRec 315 9 cnt T PL).1[i] = tabT (unpack 315 9 (T i)) := by
  simp [hRec]

theorem rec_lt {cnt i : Nat} {T PL : Nat → Nat} (hi : i < (hRec 315 9 cnt T PL).1.size) :
    i < cnt := by
  simpa [hRec] using hi

theorem bIf_or' {a b : Bool} (h : bIf(a, true, b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem knorm : atK J2Q2a.cnt J2Q2a.T J2Nin2a 0 (F 24) = true ∧
    atK J2Q2a.cnt J2Q2a.T J2Nin2a 1 (F 25) = true ∧ atK J2Q2b.cnt J2Q2b.T J2Nin2b 0 (F 27) = true ∧
    atK J2Q2b.cnt J2Q2b.T J2Nin2b 1 (F 28) = true ∧ Nat.blt (r32 J2EInv 0) J2E2a.cnt = true ∧
    involK (J2E2a.T (r32 J2EInv 0)) = true ∧ Nat.blt (r32 J2EInv 1) J2E2b.cnt = true ∧
    involK (J2E2b.T (r32 J2EInv 1)) = true := by
  simpa only [bAnd_iff] using k_norm

theorem odd_norm {r p t a b cs q : Nat} {TQ PLQ POSQ TE PLE : Nat → Nat} {cntQ cntE : Nat}
    {cg cgInv : Array Table} (hr : r < 42) (ht : t < 42) (ha : a < 42) (hb : b < 42)
    (ho : oddK r p t = true) (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1])
    (hq : conjClosureH 315 cg cgInv (j2CentTbl r) 3000 = hRec 315 9 cntQ TQ PLQ)
    (hqt : conjTreeOK 315 cg cgInv (j2CentTbl r) (hRec 315 9 cntQ TQ PLQ).1
      (hRec 315 9 cntQ TQ PLQ).2.1 (hRec 315 9 cntQ TQ PLQ).2.2 = true)
    (hTQ : ∀ i < cntQ, canonK 315 9 (mask 9) (315 * 9) (TQ i) = true)
    (hma : atK cntQ TQ POSQ 0 (F a) = true) (hmb : atK cntQ TQ POSQ 1 (F b) = true)
    (hl : [j2CentTbl a, j2CentTbl b].toArray = (cgL a 2).toArray)
    (he : mulClosureH 315 (cgL a 2).toArray 3000 = hRec 315 9 cntE TE PLE)
    (het : mulTreeOK 315 (cgL a 2).toArray (hRec 315 9 cntE TE PLE).1 (hRec 315 9 cntE TE PLE).2.1
      (hRec 315 9 cntE TE PLE).2.2 = true)
    (hTE : ∀ i < cntE, canonK 315 9 (mask 9) (315 * 9) (TE i) = true)
    (hq1 : q < cntE) (hq2 : involK (TE q) = true) :
    oddRowOK 315 3000 j2Sift (j2CentTbl t) cg cgInv
      { rep := j2CentTbl r, prime := p, classSize := cs, wit := .normal [j2CentTbl a, j2CentTbl b]
          60 } =
        true := by
  obtain ⟨a1, a2, a3, a4⟩ := oddF hr ht ho hdp
  have g1 : [j2CentTbl a, j2CentTbl b].all (fun g => permOK 315 g && memT 315
      (hRec 315 9 cntQ TQ PLQ).1 g) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [tabF ha, tabF hb]
    exact ⟨⟨permOK_unpack (Fc ha) (Finv ha), mem_at hTQ (Fc ha) hma⟩,
      permOK_unpack (Fc hb) (Finv hb), mem_at hTQ (Fc hb) hmb⟩
  have g2 : (hRec 315 9 cntE TE PLE).1.any (involOK 315) = true := by
    rw [Array.any_eq_true]
    refine ⟨q, by simpa [hRec] using hq1, ?_⟩
    rw [rec_get, involF (hTE q hq1)]
    exact hq2
  unfold oddRowOK
  simp only [a1, a2, a3, a4, Bool.true_and, hq, hqt, hl, he, het, g1, g2]

theorem invol_of {k : Nat} (hk : k < 42) (h : involK (F k) = true) : involOK 315 (j2CentTbl k) =
    true := by
  rw [tabF hk, involF (Fc hk)]
  exact h

theorem sel_tab {cnt i : Nat} {T PL : Nat → Nat}
    (hT : ∀ q < cnt, canonK 315 9 (mask 9) (315 * 9) (T q) = true)
    (hi : i < (hRec 315 9 cnt T PL).1.size) (p₁ p₂ : Nat) :
    selOK 315 [p₁, p₂] (hRec 315 9 cnt T PL).1[i] = selK p₁ p₂ (T i) := by
  rw [rec_get hi, selF (hT i (rec_lt hi))]

theorem canonR {cnt k : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : ∀ i < cnt, penumPtK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, canonK 315 9 (mask 9) (315 * 9) (T i) = true :=
  fun i hi => penumPt_canon (h i hi)

theorem sel1 : (hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).1.all (fun y => !selOK 315 [3, 7] y ||
    (memT 315 (hRec 315 9 J2Q1a.cnt J2Q1a.T J2Q1a.PL).1 y ||
      memT 315 (hRec 315 9 J2Q1b.cnt J2Q1b.T J2Q1b.PL).1 y)) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR (pe_all' k1E) i hi'
  rw [sel_tab (canonR (pe_all' k1E)) hi, rec_get hi]
  have h := allN_spec k_sel1 i hi'
  unfold sel1K at h
  rw [strictB_eq''] at h
  cases hs : selK 3 7 (J2K1.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR (pe_all' q1aE)) hc h1)
    · exact Or.inr (mem_at (canonR (pe_all' q1bE)) hc h1)

theorem sel2 : (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1.all (fun y => !selOK 315 [3, 5] y ||
    (memT 315 (hRec 315 9 J2Q2a.cnt J2Q2a.T J2Q2a.PL).1 y ||
      (memT 315 (hRec 315 9 J2Q2b.cnt J2Q2b.T J2Q2b.PL).1 y ||
        memT 315 (hRec 315 9 J2Q2c.cnt J2Q2c.T J2Q2c.PL).1 y))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR (J2Loc.pe_all J2Loc.c1E) i hi'
  rw [sel_tab (canonR (J2Loc.pe_all J2Loc.c1E)) hi, rec_get hi]
  have h := allN_spec k_sel2 i hi'
  unfold sel2K at h
  rw [strictB_eq''] at h
  cases hs : selK 3 5 (J2C1.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR (pe_all' q2aE)) hc h1)
    rcases bIf_or' h1 with h2 | h2
    · exact Or.inr (Or.inl (mem_at (canonR (pe_all' q2bE)) hc h2))
    · exact Or.inr (Or.inr (mem_at (canonR (pe_all' q2cE)) hc h2))

theorem sel3_all : ∀ i < J2C2.cnt, sel3K i = true := by
  have hc : J2C2.cnt = 320 * 6 := rfl
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2C2.cnt := by rw [hc]; omega
  interval_cases s
  · exact slK_spec sel3_0 i h1 h2 hi
  · exact slK_spec sel3_1 i h1 h2 hi
  · exact slK_spec sel3_2 i h1 h2 hi
  · exact slK_spec sel3_3 i h1 h2 hi
  · exact slK_spec sel3_4 i h1 h2 hi
  · exact slK_spec sel3_5 i h1 h2 hi

theorem sel3 : (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1.all (fun y => !selOK 315 [3, 5] y ||
    (memT 315 (hRec 315 9 J2Q3a.cnt J2Q3a.T J2Q3a.PL).1 y ||
      (memT 315 (hRec 315 9 J2Q3b.cnt J2Q3b.T J2Q3b.PL).1 y ||
        memT 315 (hRec 315 9 J2Q3c.cnt J2Q3c.T J2Q3c.PL).1 y))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR J2Loc.c2_pe i hi'
  rw [sel_tab (canonR J2Loc.c2_pe) hi, rec_get hi]
  have h := sel3_all i hi'
  unfold sel3K at h
  rw [strictB_eq''] at h
  cases hs : selK 3 5 (J2C2.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR (pe_all' q3aE)) hc h1)
    rcases bIf_or' h1 with h2 | h2
    · exact Or.inr (Or.inl (mem_at (canonR (pe_all' q3bE)) hc h2))
    · exact Or.inr (Or.inr (mem_at (canonR (pe_all' q3cE)) hc h2))

theorem row1 : CFSG.Sporadic.SmallOddCore.classOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift
    j2OuterTbl
    { rep := j2CentTbl 9, outer := true, classSize := 1800, centOrder := 336,
      centGens := [j2CentTbl 10, j2CentTbl 11, j2CentTbl 12], oddPrimes := [3, 7],
      odd := [{ rep := j2CentTbl 13, prime := 7, classSize := 48, wit := .conj (j2CentTbl 14) 4 },
        { rep := j2CentTbl 15, prime := 3, classSize := 56, wit := .conj (j2CentTbl 16) 4 }] }
    (conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 9) 3000) = true := by
  have e : [j2CentTbl 10, j2CentTbl 11, j2CentTbl 12] = cgL 10 3 := rfl
  have o1 := odd_conj (r := 13) (p := 7) (h := 14) (t := 9) (ord := 4) (cs := 48)
    (cg := (cgL 10 3).toArray) (cgInv := (cgL 10 3).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.1 (by decide) kconj.1 (ord4 kord.1) (by norm_num)
    (by norm_num)
  have o2 := odd_conj (r := 15) (p := 3) (h := 16) (t := 9) (ord := 4) (cs := 56)
    (cg := (cgL 10 3).toArray) (cgInv := (cgL 10 3).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.1 (by decide) kconj.2.1 (ord4 kord.2.1) (by norm_num)
    (by norm_num)
  have hrep : (!j2Sift (j2CentTbl 9) && j2Sift (compT 315 (j2CentTbl 9) j2OuterTbl)) = true := by
    rw [siftF (by norm_num), u_tab, tabF (by norm_num), compT_unpack (Fc (by norm_num))
      (Fc (by norm_num)), sift_eq (compF (Fc (by norm_num)) (Fc (by norm_num))),
      notB (b := sK (F 9)) kreps.2.2.2.1]
    exact kreps.2.2.2.2.1
  have s1 : ((hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).1.size == 1800) = true := by
    rw [hRec_size, sizes.1]
    rfl
  have s2 : ((hRec 315 9 J2K1.cnt J2K1.T J2K1.PL).1.size == 336) = true := by
    rw [hRec_size, sizes.2.2.2.2.1]
    rfl
  unfold CFSG.Sporadic.SmallOddCore.classOK
  simp only [e, recR1.1, recK1.1, recQ1a.1, recQ1b.1, recR1.2.1, recR1.2.2, recK1.2.1, recK1.2.2,
    recQ1a.2.1, recQ1b.2.1, s1, s2, permF (k := 9) (by norm_num),
    invol_of (k := 9) (by norm_num) kreps.1, hrep, cg_all 10 3 9 (by norm_num) (by norm_num) kcg.1,
    o1, o2, sel1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, ↓reduceIte, Bool.and_true, Bool.or_false, beq_self_eq_true]

theorem hc1 : J2C1.cnt = 240 := rfl

theorem hc2 : J2C2.cnt = 1920 := rfl

theorem row2 : CFSG.Sporadic.SmallOddCore.classOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift
    j2OuterTbl
    { rep := j2CentTbl 17, outer := false, classSize := 2520, centOrder := 240,
      centGens := [j2CentTbl 18, j2CentTbl 19, j2CentTbl 20, j2CentTbl 21, j2CentTbl 22],
      oddPrimes := [3, 5],
      odd := [
        { rep := j2CentTbl 23, prime := 5, classSize := 12,
          wit := .normal [j2CentTbl 24, j2CentTbl 25] 60 },
        { rep := j2CentTbl 26, prime := 5, classSize := 12,
          wit := .normal [j2CentTbl 27, j2CentTbl 28] 60 },
        { rep := j2CentTbl 29, prime := 3, classSize := 20, wit := .conj (j2CentTbl 30) 2 }] }
    (conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 17) 3000) = true := by
  have e : [j2CentTbl 18, j2CentTbl 19, j2CentTbl 20, j2CentTbl 21, j2CentTbl 22] = cgL 18 5 := rfl
  have o1 := odd_norm (r := 23) (p := 5) (t := 17) (a := 24) (b := 25) (cs := 12)
    (cg := (cgL 18 5).toArray) (cgInv := (cgL 18 5).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) kodd.2.2.1 (by decide) recQ2a.1 recQ2a.2.1
    (canonR (pe_all' q2aE)) knorm.1 knorm.2.1 rfl recE2a.1 recE2a.2.1 (canonR (pe_all' e2aE))
    (Nat.le_of_ble_eq_true knorm.2.2.2.2.1) knorm.2.2.2.2.2.1
  have o2 := odd_norm (r := 26) (p := 5) (t := 17) (a := 27) (b := 28) (cs := 12)
    (cg := (cgL 18 5).toArray) (cgInv := (cgL 18 5).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) kodd.2.2.2.1 (by decide) recQ2b.1 recQ2b.2.1
    (canonR (pe_all' q2bE)) knorm.2.2.1 knorm.2.2.2.1 rfl recE2b.1 recE2b.2.1
    (canonR (pe_all' e2bE)) (Nat.le_of_ble_eq_true knorm.2.2.2.2.2.2.1) knorm.2.2.2.2.2.2.2
  have o3 := odd_conj (r := 29) (p := 3) (h := 30) (t := 17) (ord := 2) (cs := 20)
    (cg := (cgL 18 5).toArray) (cgInv := (cgL 18 5).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.1 (by decide) kconj.2.2.1 (ord2 kord.2.2.1)
    (by norm_num) (by norm_num)
  have hrep : j2Sift (j2CentTbl 17) = true := by
    rw [siftF (by norm_num)]
    exact kreps.2.2.2.2.2.1
  have s1 : ((hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).1.size == 2520) = true := by
    rw [hRec_size, sizes.2.1]
    rfl
  have s2 : ((hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1.size == 240) = true := by
    rw [hRec_size, hc1]
    rfl
  unfold CFSG.Sporadic.SmallOddCore.classOK
  simp only [e, recR2.1, recC1.1, recQ2a.1, recQ2b.1, recQ2c.1, recR2.2.1, recR2.2.2, recC1.2.1,
    recC1.2.2, recQ2a.2.1, recQ2b.2.1, recQ2c.2.1, s1, s2,
    permF (k := 17) (by norm_num), invol_of (k := 17) (by norm_num) kreps.2.1, hrep,
    cg_all 18 5 17 (by norm_num) (by norm_num) kcg.2.1, o1, o2, o3, sel2, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, ↓reduceIte,
    Bool.and_true, Bool.or_false, beq_self_eq_true, Bool.false_eq_true]

theorem row3 : CFSG.Sporadic.SmallOddCore.classOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift
    j2OuterTbl
    { rep := j2CentTbl 31, outer := false, classSize := 315, centOrder := 1920,
      centGens := [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35], oddPrimes := [3, 5],
      odd := [{ rep := j2CentTbl 36, prime := 3, classSize := 80, wit := .conj (j2CentTbl 37) 6 },
        { rep := j2CentTbl 38, prime := 5, classSize := 192, wit := .conj (j2CentTbl 39) 4 },
        { rep := j2CentTbl 40, prime := 5, classSize := 192, wit := .conj (j2CentTbl 41) 4 }] }
    (conjClosureH 315 j2PGTbls j2PGInvTbls (j2CentTbl 31) 3000) = true := by
  have e : [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35] = cgL 32 4 := rfl
  have o1 := odd_conj (r := 36) (p := 3) (h := 37) (t := 31) (ord := 6) (cs := 80)
    (cg := (cgL 32 4).toArray) (cgInv := (cgL 32 4).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.1 (by decide) kconj.2.2.2.1 (ord6 kord.2.2.2.1)
    (by norm_num) (by norm_num)
  have o2 := odd_conj (r := 38) (p := 5) (h := 39) (t := 31) (ord := 4) (cs := 192)
    (cg := (cgL 32 4).toArray) (cgInv := (cgL 32 4).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.1 (by decide) kconj.2.2.2.2.1
    (ord4 kord.2.2.2.2.1) (by norm_num) (by norm_num)
  have o3 := odd_conj (r := 40) (p := 5) (h := 41) (t := 31) (ord := 4) (cs := 192)
    (cg := (cgL 32 4).toArray) (cgInv := (cgL 32 4).toArray.map (invT 315)) (by norm_num)
    (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.2 (by decide) kconj.2.2.2.2.2
    (ord4 kord.2.2.2.2.2) (by norm_num) (by norm_num)
  have hrep : j2Sift (j2CentTbl 31) = true := by
    rw [siftF (by norm_num)]
    exact kreps.2.2.2.2.2.2
  have s1 : ((hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).1.size == 315) = true := by
    rw [hRec_size, sizes.2.2.1]
    rfl
  have s2 : ((hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1.size == 1920) = true := by
    rw [hRec_size, hc2]
    rfl
  unfold CFSG.Sporadic.SmallOddCore.classOK
  simp only [e, recR3.1, recC2.1, recQ3a.1, recQ3b.1, recQ3c.1, recR3.2.1, recR3.2.2, recC2.2.1,
    recC2.2.2, recQ3a.2.1, recQ3b.2.1, recQ3c.2.1, s1, s2,
    permF (k := 31) (by norm_num), invol_of (k := 31) (by norm_num) kreps.2.2.1, hrep,
    cg_all 32 4 31 (by norm_num) (by norm_num) kcg.2.2, o1, o2, o3, sel3, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, ↓reduceIte,
    Bool.and_true, Bool.or_false, beq_self_eq_true, Bool.false_eq_true]

theorem scov_all : (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).1.all (fun s => !involOK 315 s ||
    (memT 315 (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).1 s ||
      (memT 315 (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).1 s ||
        memT 315 (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).1 s))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' := rec_lt hi
  have hc := canonR (pe_all' syE) i hi'
  rw [rec_get hi, involF hc]
  have h := allN_spec k_scov i hi'
  unfold scovK at h
  rw [strictB_eq''] at h
  cases hs : involK (J2SY.T i)
  · rfl
  · rw [hs] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true]
    rcases bIf_or' h with h1 | h1
    · exact Or.inl (mem_at (canonR r1_pe) hc h1)
    rcases bIf_or' h1 with h2 | h2
    · exact Or.inr (Or.inl (mem_at (canonR r2_pe) hc h2))
    · exact Or.inr (Or.inr (mem_at (canonR (pe_all' o3E)) hc h2))

theorem kucov : ucovK 0 9 = true ∧ ucovK 1 17 = true ∧ ucovK 2 31 = true := by
  simpa only [bAnd_iff] using k_ucov

theorem ucov_of {i t : Nat} (ht : t < 42) (h : ucovK i t = true) :
    (memT 315 (hRec 315 9 J2R1.cnt J2R1.T J2R1.PL).1
        (conjT 315 j2OuterTbl (invT 315 j2OuterTbl) (j2CentTbl t)) ||
      (memT 315 (hRec 315 9 J2R2.cnt J2R2.T J2R2.PL).1
          (conjT 315 j2OuterTbl (invT 315 j2OuterTbl) (j2CentTbl t)) ||
        memT 315 (hRec 315 9 J2R3.cnt J2R3.T J2R3.PL).1
          (conjT 315 j2OuterTbl (invT 315 j2OuterTbl) (j2CentTbl t)))) = true := by
  have hu : j2OuterTbl = j2CentTbl 0 := rfl
  rw [hu, invF (by norm_num), tabF (by norm_num), tabF ht,
    conjT_unpack (Fc (by norm_num)) (Ic (by norm_num)) (Fc ht)]
  have hy := compF (compF (Fc (k := 0) (by norm_num)) (Fc ht)) (Ic (k := 0) (by norm_num))
  unfold ucovK at h
  rw [strictB_eq''] at h
  simp only [Bool.or_eq_true]
  rcases bIf_or' h with h1 | h1
  · exact Or.inl (mem_at (canonR r1_pe) hy h1)
  rcases bIf_or' h1 with h2 | h2
  · exact Or.inr (Or.inl (mem_at (canonR r2_pe) hy h2))
  · exact Or.inr (Or.inr (mem_at (canonR (pe_all' o3E)) hy h2))

@[expose] noncomputable def noneK (k : Nat) (f : Nat → Bool) : Bool :=
  allN k (fun j => bIf(f j, false, true))

theorem k_stab : bAnd(allN 7 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2P.S j)),
    bAnd(allN 7 (fun j => bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1, sK (J2P.S j), true)),
    allN 315 (fun x => bIf(Nat.beq x 1, true, bIf(noneK 7 (fun j =>
      bAnd(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1,
        bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) x) x, false, true))), false, true))))) = true := by
  quickRfl

theorem stab_facts : allN 7 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2P.S j)) = true ∧
    allN 7 (fun j => bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1, sK (J2P.S j), true)) = true ∧
    allN 315 (fun x => bIf(Nat.beq x 1, true, bIf(noneK 7 (fun j =>
      bAnd(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1,
        bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) x) x, false, true))), false, true))) = true := by
  simpa only [bAnd_iff] using k_stab

theorem strong_tab {j : Nat} (hj : j < 7) :
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]!.map UInt32.ofNat =
      tabT (unpack 315 9 (J2P.S j)) := by
  rw [J2PC.bindsP.2.2.2.2.1 j hj]
  rfl

theorem ap_S {j x : Nat} (hj : j < 7) (hx : x < 315) :
    ap (tabT (unpack 315 9 (J2P.S j))) x = pg 9 (mask 9) (J2P.S j) x := by
  rw [ap_tabT _ (unpack_lt (allN_spec stab_facts.1 j hj)), CFSG.KC.Misc.PairCount.unpack_get hx]

theorem stab_mem {s : Table} (hs : s ∈ ((List.range 7).map fun j =>
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]!.map UInt32.ofNat)) :
    ∃ j < 7, s = tabT (unpack 315 9 (J2P.S j)) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
  exact ⟨j, List.mem_range.1 hj, strong_tab (List.mem_range.1 hj)⟩

theorem stab_ok : j2StabOK = true := by
  unfold j2StabOK j2StabTbls
  simp only [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro s hs
    rw [List.mem_filter] at hs
    obtain ⟨hm, hp⟩ := hs
    obtain ⟨j, hj, rfl⟩ := stab_mem hm
    rw [ap_S hj (by norm_num)] at hp
    have h := allN_spec stab_facts.2.1 j hj
    have hb : Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1 = true := by simpa using hp
    rw [hb] at h
    rw [sift_eq (allN_spec stab_facts.1 j hj), ap_S hj (by norm_num)]
    simp only [Bool.and_eq_true]
    exact ⟨h, hp⟩
  · rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    have h := allN_spec stab_facts.2.2 x hx'
    cases e : Nat.beq x 1
    · rw [e] at h
      have hn := notB h
      unfold noneK at hn
      have hex : ∃ j < 7, bAnd(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1,
          bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) x) x, false, true)) = true := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have : allN 7 (fun j => bIf(bAnd(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1,
            bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) x) x, false, true)), false, true)) = true := by
          rw [allN_iff]
          intro j hj
          have := hne j hj
          revert this
          cases bAnd(Nat.beq (pg 9 (mask 9) (J2P.S j) 1) 1,
            bIf(Nat.beq (pg 9 (mask 9) (J2P.S j) x) x, false, true)) <;> simp
        rw [this] at hn
        exact absurd hn (by decide)
      obtain ⟨j, hj, hjx⟩ := hex
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hjx
      have hne1 : x ≠ 1 := fun h1 => by
        rw [h1] at e
        exact absurd e (by decide)
      have hxe : (x == 1) = false := by simp [hne1]
      simp only [hxe, Bool.false_or, List.any_eq_true, List.mem_filter]
      refine ⟨_, ⟨List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩, ?_⟩
      · rw [strong_tab hj, ap_S hj (by norm_num), Nat.eq_of_beq_eq_true h1]
        rfl
      · rw [strong_tab hj, ap_S hj hx', bne_iff_ne]
        intro hq
        rw [hq, Nat.beq_refl] at h2
        exact absurd h2 (by decide)
    · have : x = 1 := Nat.eq_of_beq_eq_true e
      subst this
      rfl

theorem facts2278 : (j2StabOK = true) ∧
    (centDataOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift j2OuterTbl j2SylowGenTbls j2SylowOrder
      j2Rows = true) := by
  refine ⟨stab_ok, ?_⟩
  unfold centDataOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨syl_ok, ?_⟩, ?_⟩
  · simp only [j2Rows, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨row1, row2, row3⟩
  · unfold coverOK
    simp only [j2Rows, sy_eq, recSY.1, recR1.1, recR2.1, recR3.1, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false,
      Bool.and_eq_true]
    exact ⟨scov_all, ucov_of (by norm_num) kucov.1, ucov_of (by norm_num) kucov.2.1,
      ucov_of (by norm_num) kucov.2.2⟩

end CertificateChecks.KernelSpor.J2Cn

end
