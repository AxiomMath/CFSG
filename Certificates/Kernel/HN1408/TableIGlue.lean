module

public import Certificates.Kernel.HN1408.TableIChk
public import Certificates.Kernel.HN1408.TableIR1
public import Certificates.Kernel.HN1408.TableIC1
public import Certificates.Kernel.HN1408.TableIR3
public import Certificates.Kernel.HN1408.TableIC3
public import Certificates.Kernel.HN1408.TableIL
public import Certificates.Kernel.HN1408.TableILS
public import Certificates.Kernel.HN1408.BlkGlue
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.PEnumRSound
import Certificates.Kernel.HN1408.Spec
import CFSG.Certificates.Kernel.Spor.PEnumBSound
public import Certificates.Kernel.HN1408.EnumH

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.KC.Blk
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KLie.CT (andB orB notB anyN)

#kc_forall_chunks peL2_all (fun s => peL2 s = true) 10 CFSG.KD.HN1408.peL2 1
#kc_forall_chunks hsL2_all (fun s => hsL2 s = true) 10 CFSG.KD.HN1408.hsL2 1
#kc_forall_chunks clL2_all (fun s => clL2 s = true) 10 CFSG.KD.HN1408.clL2 1
#kc_forall_chunks peLS_all (fun s => peLS s = true) 10 CFSG.KD.HN1408.peLS 1
#kc_forall_chunks hsLS_all (fun s => hsLS s = true) 10 CFSG.KD.HN1408.hsLS 1
#kc_forall_chunks clLS_all (fun s => clLS s = true) 10 CFSG.KD.HN1408.clLS 1
#kc_forall_chunks pe1_all (fun s => pe1 s = true) 4 CFSG.KD.HN1408.pe1 1
#kc_forall_chunks hv1_all (fun s => hv1 s = true) 2 CFSG.KD.HN1408.hv1 1
#kc_forall_chunks cl1_all (fun s => cl1 s = true) 8 CFSG.KD.HN1408.cl1 1
#kc_forall_chunks pe3_all (fun s => pe3 s = true) 4 CFSG.KD.HN1408.pe3 1
#kc_forall_chunks hv3_all (fun s => hv3 s = true) 4 CFSG.KD.HN1408.hv3 1
#kc_forall_chunks cl3_all (fun s => cl3 s = true) 8 CFSG.KD.HN1408.cl3 1

theorem bA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff _ _).1 h

abbrev HeadSpec (ws : List (List Nat)) (k m : Nat) (G GI GJ T PL : Nat → Nat) (cnt : Nat) : Prop :=
  ws.length = k ∧ (∀ j < k, GI j = WK (ws.getD j []) ∧ G j = idK ∧
    canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true) ∧ cnt = m ∧
    penumHdK idK cnt 100000 T PL = true

theorem headI_spec {ws : List (List Nat)} {k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (h : headI ws k m G GI GJ T PL cnt = true) : HeadSpec ws k m G GI GJ T PL cnt := by
  unfold headI at h
  obtain ⟨h1, h2⟩ := bA h
  obtain ⟨h3, h4⟩ := bA h2
  obtain ⟨h5, h6⟩ := bA h4
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_, Nat.eq_of_beq_eq_true h5, h6⟩
  have h7 := allN_spec h3 j hj
  obtain ⟨a, h8⟩ := bA h7
  obtain ⟨b, h9⟩ := bA h8
  obtain ⟨c, d⟩ := bA h9
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩

theorem rec_of_spec {ws : List (List Nat)} {k m cnt : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (h : HeadSpec ws k m G GI GJ T PL cnt)
    (hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 1408 11 (mask 11) (k + k) T (bothK k GI GJ)) CL c = true) :
    enumW capI m ws = true ∧ subgroupList capI ws = (hRec 1408 11 cnt T PL).1 ∧
      ∀ i < cnt, Cn (T i) := by
  obtain ⟨hk, hg, hm, hh⟩ := h
  subst hk
  obtain ⟨e1, e2⟩ := enumW_of (cap := capI) hl (fun j hj => (hg j hj).2.1) (fun j hj => (hg j hj).1)
    (fun j hj => ⟨(hg j hj).2.2.2, (hg j hj).2.2.1⟩) hh hp hs hcl hm
  exact ⟨e1, e2, fun i hi => penumPt_canon (hp i hi)⟩

theorem rec_of {ws : List (List Nat)} {k m cnt : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (h : headI ws k m G GI GJ T PL cnt = true)
    (hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 1408 11 (mask 11) (k + k) T (bothK k GI GJ)) CL c = true) :
    enumW capI m ws = true ∧ subgroupList capI ws = (hRec 1408 11 cnt T PL).1 ∧
      ∀ i < cnt, Cn (T i) :=
  rec_of_spec hl (headI_spec h) hp hs hcl

theorem hl1 : ∀ w ∈ nWords1, lettersOK w = true := by decide
theorem hl2 : ∀ w ∈ sWords2, lettersOK w = true := by decide
theorem hl3 : ∀ w ∈ sWords3, lettersOK w = true := by decide
theorem hl4 : ∀ w ∈ nWords3, lettersOK w = true := by decide

abbrev RecFacts (ws : List (List Nat)) (m cnt : Nat) (T PL : Nat → Nat) : Prop :=
  enumW capI m ws = true ∧ subgroupList capI ws = (hRec 1408 11 cnt T PL).1 ∧ ∀ i < cnt, Cn (T i)

theorem recR_of {ws : List (List Nat)} {k m cnt : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI HV CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (h : HeadSpec ws k m G GI GJ T PL cnt)
    (hp : ∀ i < cnt, CFSG.KS.PEnumR.penumPtR 1408 11 (mask 11) GI k cnt T PL POS SRT SRI i = true)
    (hv : ∀ i < cnt, CFSG.KS.PEnumR.hvF 1408 11 (mask 11) T HV i = true)
    (hs : ∀ i < cnt, CFSG.KS.PEnumB.hsortVK cnt HV HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 1408 11 (mask 11) (k + k) T (bothK k GI GJ)) CL c = true) :
    RecFacts ws m cnt T PL := by
  obtain ⟨hk, hg, -, hh⟩ := id h
  have hGI : ∀ j < k, canonK 1408 11 (mask 11) (1408 * 11) (GI j) = true := by
    intro j hj
    have hm : ws.getD j [] ∈ ws := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ws.length by omega),
        Option.getD_some]
      exact List.getElem_mem _
    rw [(hg j hj).1]
    exact (tabW_eq (hl _ hm)).2
  exact rec_of_spec hl h
    (CFSG.KS.PEnumR.penumPtK_of_R hn hGI (fun j hj => (hg j hj).2.1) hh hp)
    (CFSG.KS.PEnumB.hsortPtK_of_V
      (fun i hi => by rw [← CFSG.KS.PEnumR.hvF_eq (n := 1408) (by decide)]; exact hv i hi) hs) hcl

theorem kR4' : pe4 = true ∧ hs4 = true ∧ cl4 = true := by
  have h := kR4
  simp only [bAnd_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem r1 : RecFacts nWords1 256 TI1.cnt TI1.T TI1.PL := by
  have hc : TI1.cnt = 256 := (headI_spec kH1).2.2.1
  have hs := kS1
  unfold hs1 at hs
  exact recR_of hl1 (headI_spec kH1)
    (slAll (L := 64) (K := 4) (by rw [hc]) fun s hs => pe1_all s hs)
    (slAll (L := 128) (K := 2) (by rw [hc]) fun s hs => hv1_all s hs)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by rw [hc] at hi; omega) hi)
    (slAll (L := 448) (K := 8) (by rw [hc]) fun s hs => cl1_all s hs)

theorem cnt3 : TI3.cnt = 960 := (headI_spec kH3).2.2.1

theorem r3 : RecFacts sWords3 960 TI3.cnt TI3.T TI3.PL := by
  have hs := kS3
  unfold hs3 at hs
  exact recR_of hl3 (headI_spec kH3)
    (slAll (L := 240) (K := 4) (by rw [cnt3]) fun s hs => pe3_all s hs)
    (slAll (L := 240) (K := 4) (by rw [cnt3]) fun s hs => hv3_all s hs)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by rw [cnt3] at hi; omega) hi)
    (slAll (L := 480) (K := 8) (by rw [cnt3]) fun s hs => cl3_all s hs)

theorem map_two {α β : Type} (f : α → β) (d : α) {l : List α} (h : l.length = 2) :
    l.map f = [f (l.getD 0 d), f (l.getD 1 d)] := by
  match l, h with
  | [_, _], _ => rfl

theorem kH4spec : HeadSpec nWords3 4 16 TI4.G TI4.GI J4 TI4.T TI4.PL TI4.cnt := by
  have h := kH4
  unfold headI4 at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h5, h6⟩ := h
  obtain ⟨hk3, hg3, -, -⟩ := headI_spec kH3
  have hS : sWords3.map WK = [TI3.GI 0, TI3.GI 1] := by
    rw [map_two WK [] hk3, ← (hg3 0 (by omega)).1, ← (hg3 1 (by omega)).1]
  refine ⟨?_, fun j hj => ?_, Nat.eq_of_beq_eq_true h5, h6⟩
  · rw [nWords3, List.length_map]
    exact Nat.eq_of_beq_eq_true h1
  · have h7 := allN_spec h3 j hj
    simp only [bAnd_iff] at h7
    obtain ⟨a, b, c, d⟩ := h7
    have e : nWords3.getD j [] = specWord sWords3 (nSpec3.getD j []) := by
      rw [nWords3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases nSpec3[j]? <;> rfl
    refine ⟨?_, Nat.eq_of_beq_eq_true b, c, d⟩
    rw [Nat.eq_of_beq_eq_true a, e, WK_specWord hl3, hS]

theorem r4 : RecFacts nWords3 16 TI4.cnt TI4.T TI4.PL := by
  obtain ⟨hp, hs, hc⟩ := kR4'
  unfold pe4 at hp
  unfold hs4 at hs
  unfold cl4 at hc
  exact rec_of_spec hl4 kH4spec
    (fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc' => slK_spec hc c (Nat.zero_le _) (by change c < Nat.mul TI4.cnt 8; omega)
      (by change c < Nat.mul TI4.cnt 8; omega))


theorem headL_spec {k m cnt : Nat} {L : List Table} {G GI GJ T PL : Nat → Nat}
    (h : headL k L m G GI GJ T PL cnt = true) :
    L.length = 2 ∧ (∀ j < 2, L.getD j #[] = tabT (unpack k 4 (GI j)) ∧ G j = pidn k 4 ∧
      canonK k 4 (mask 4) (k * 4) (GI j) = true ∧ canonK k 4 (mask 4) (k * 4) (GJ j) = true ∧
      invEqK k 4 (mask 4) (k * 4) (GI j) (GJ j) = true) ∧ cnt = m ∧ szOK k 4 = true ∧
      penumHdK (pidn k 4) cnt 100000 T PL = true := by
  unfold headL at h
  obtain ⟨h1, h2⟩ := bA h
  obtain ⟨h3, h4⟩ := bA h2
  obtain ⟨h5, h6⟩ := bA h4
  obtain ⟨h7, h8⟩ := bA h6
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_, Nat.eq_of_beq_eq_true h5, h7, h8⟩
  have h9 := allN_spec h3 j hj
  obtain ⟨a, h10⟩ := bA h9
  obtain ⟨b, h11⟩ := bA h10
  obtain ⟨c, h12⟩ := bA h11
  obtain ⟨d, e⟩ := bA h12
  refine ⟨?_, Nat.eq_of_beq_eq_true b, c, d, e⟩
  rw [← tabT_natArr (L.getD j #[]), eq_unpack_of_bindListK a]

theorem labTabs {k m cnt : Nat} {L : List Table} {G GI GJ T PL : Nat → Nat}
    (h : headL k L m G GI GJ T PL cnt = true) : TabsOK k 4 2 GI L.toArray := by
  obtain ⟨hl, hg, -⟩ := headL_spec h
  refine ⟨by simp [hl], fun j hj => ⟨?_, (hg j hj).2.2.1⟩⟩
  rw [← (hg j hj).1, getElem!_pos _ j (by simp [hl, hj]), List.getElem_toArray,
    List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]

theorem img_of {k m cnt : Nat} {L : List Table} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (h : headL k L m G GI GJ T PL cnt = true)
    (hp : ∀ i < cnt, penumPtK k 4 (mask 4) (k * 4) true G GI 2 cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK k 4 (mask 4) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (2 + 2), findPtK cnt T (prodQK k 4 (mask 4) (2 + 2) T (bothK 2 GI GJ)) CL c =
      true) : CFSG.Sporadic.SmallOddCore.enumOK k 100000 m L = true := by
  obtain ⟨-, hg, hm, hsz, hh⟩ := headL_spec h
  exact enumOK_of hsz (fun j hj => (hg j hj).2.1) (labTabs h)
    (fun j hj => ⟨(hg j hj).2.2.2.2, (hg j hj).2.2.2.1⟩) hh hp hs hcl hm

theorem kL1' : headL 5 labs1 120 TL1.G TL1.GI TL1J TL1.T TL1.PL TL1.cnt = true ∧ peL1 = true ∧
    hsL1 = true ∧ clL1 = true := by
  have h := kL1
  simp only [bAnd_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem kL3' : headL 5 labs3 60 TL3.G TL3.GI TL3J TL3.T TL3.PL TL3.cnt = true ∧ peL3 = true ∧
    hsL3 = true ∧ clL3 = true := by
  have h := kL3
  simp only [bAnd_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem img1 : blkImageOK blkData1 120 = true := by
  obtain ⟨hh, hp, hs, hc⟩ := kL1'
  unfold peL1 at hp
  unfold hsL1 at hs
  unfold clL1 at hc
  exact img_of hh
    (fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc' => slK_spec hc c (Nat.zero_le _) (by change c < Nat.mul TL1.cnt 4; omega)
      (by change c < Nat.mul TL1.cnt 4; omega))

theorem img3 : blkImageOK blkData3 60 = true := by
  obtain ⟨hh, hp, hs, hc⟩ := kL3'
  unfold peL3 at hp
  unfold hsL3 at hs
  unfold clL3 at hc
  exact img_of hh
    (fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc' => slK_spec hc c (Nat.zero_le _) (by change c < Nat.mul TL3.cnt 4; omega)
      (by change c < Nat.mul TL3.cnt 4; omega))

theorem img2 : blkImageOK blkData2 20160 = true := by
  have hc : TL2.cnt = 20160 := (headL_spec kL2h).2.2.1
  exact img_of kL2h
    (peAll (L := 2016) (K := 10) (by rw [hc]) fun s hs => peL2_all s hs)
    (slAll (L := 2016) (K := 10) (by rw [hc]) fun s hs => hsL2_all s hs)
    (slAll (L := 8064) (K := 10) (by rw [hc]) fun s hs => clL2_all s hs)

theorem imgS : blkImageOK blkData2S 20160 = true := by
  have hc : TLS.cnt = 20160 := (headL_spec kLSh).2.2.1
  exact img_of kLSh
    (peAll (L := 2016) (K := 10) (by rw [hc]) fun s hs => peLS_all s hs)
    (slAll (L := 2016) (K := 10) (by rw [hc]) fun s hs => hsLS_all s hs)
    (slAll (L := 8064) (K := 10) (by rw [hc]) fun s hs => clLS_all s hs)

theorem blkDataOK_of {d : BlkData} {i : Nat} {k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (hb : d.blk = unpack 1408 4 (TB.F i)) (hk : d.k = k) (hlen : d.gens.length = 2)
    (hw : ∀ w ∈ d.gens, lettersOK w = true) (h : headL k d.labs m G GI GJ T PL cnt = true)
    (hB : blkK i k d.gens GI = true) : blkDataOK d = true := by
  obtain ⟨hl, hg, -⟩ := headL_spec h
  unfold blkK at hB
  obtain ⟨h1, h2⟩ := bA hB
  obtain ⟨h3, h4⟩ := bA h2
  unfold blkDataOK
  rw [hb, hk, gensOK_true, blkLe_of h1, CFSG.KC.L34KSnd.size_unpack, blkSurjOK_of h3, hlen, hl]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun w hw' => wordOK_of (hw w hw'), fun L hL => ?_⟩, fun q hq => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    have hj' : j < 2 := by rw [hl] at hj; exact hj
    rw [← List.getD_eq_getElem _ #[] hj, (hg j hj').1]
    exact permOK_unpack (hg j hj').2.2.1 (hg j hj').2.2.2.2
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hj' : j < 2 := by simp [hl, hlen] at hj; omega
    rw [List.getElem_zip]
    have hw' : d.gens[j]'(by rw [hlen]; exact hj') ∈ d.gens := List.getElem_mem _
    obtain ⟨e, c⟩ := tabW_eq (hw _ hw')
    rw [e, ← List.getD_eq_getElem _ #[] (by rw [hl]; exact hj'), (hg j hj').1]
    have hm := allN_spec h4 j hj'
    rw [← List.getD_eq_getElem _ [] (by rw [hlen]; exact hj')] at c ⊢
    exact blkMapOK_of c (hg j hj').2.2.1 hm

theorem blk1 : blkData1.blk = unpack 1408 4 (TB.F 0) := blk_eq TB1.eq kB1
theorem blk2 : blkData2.blk = unpack 1408 4 (TB.F 1) := blk_eq TB2.eq kB2
theorem blk3 : blkData3.blk = unpack 1408 4 (TB.F 2) := blk_eq TB3.eq kB3

theorem dat1 : blkDataOK blkData1 = true :=
  blkDataOK_of blk1 rfl rfl (by decide) kL1'.1 kD1
theorem dat2 : blkDataOK blkData2 = true := blkDataOK_of blk2 rfl rfl (by decide) kL2h kD2
theorem datS : blkDataOK blkData2S = true := blkDataOK_of blk2 rfl rfl hl2 kLSh kDS
theorem dat3 : blkDataOK blkData3 = true :=
  blkDataOK_of blk3 rfl (by decide) hl3 kL3'.1 kD3

theorem allW {ws : List (List Nat)} {k : Nat} {GI : Nat → Nat} (hk : ws.length = k)
    (hg : ∀ j < k, GI j = WK (ws.getD j [])) (hl : ∀ w ∈ ws, lettersOK w = true) {f : Table → Bool}
    (h : ∀ j < k, f (tabT (unpack 1408 11 (GI j))) = true) : ws.all (fun w => f (tabW w)) = true := by
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have hj' : j < k := hk ▸ hj
  rw [(tabW_eq (hl _ hw)).1, ← List.getD_eq_getElem _ [] hj, ← hg j hj']
  exact h j hj'

theorem cnW {ws : List (List Nat)} {k : Nat} {GI : Nat → Nat}
    (hg : ∀ j < k, GI j = WK (ws.getD j [])) (hl : ∀ w ∈ ws, lettersOK w = true) (hk : ws.length = k) :
    ∀ j < k, Cn (GI j) := by
  intro j hj
  rw [hg j hj]
  have hw : ws.getD j [] ∈ ws := by
    rw [List.getD_eq_getElem _ _ (hk ▸ hj)]
    exact List.getElem_mem _
  exact (tabW_eq (hl _ hw)).2

abbrev WT (wd : List Nat) : Prop := tabW wd = tabT (unpack 1408 11 (WK wd)) ∧ Cn (WK wd)

theorem wA : WT wordA := tabW_eq (by decide)
theorem wZ : WT wordZ := tabW_eq (by decide)
theorem wB : WT wordB := tabW_eq (by decide)
theorem wZ1 : WT wordZ₁ := tabW_eq (by decide)
theorem wAZ : WT wordAZ := tabW_eq (by decide)
theorem wAZ1 : WT (wordA ++ wordZ₁) := tabW_eq (by decide)

theorem tI1 : tableI1OK = true := by
  obtain ⟨hk, hg, -, -⟩ := headI_spec kH1
  obtain ⟨e1, e2, hT⟩ := r1
  have hc := cnW (fun j hj => (hg j hj).1) hl1 hk
  have t := kT1
  simp only [bAnd_iff] at t
  obtain ⟨t1, t3, t5, t7, t9, t10⟩ := t
  have t1' : ∀ j < 7, blkTrivK 1408 11 4 (TB.F 0) (TI1.GI j) = true ∧
      commP (TI1.GI j) (WK wordZ) = true := by
    intro j hj
    have h := allN_spec t1 j hj
    simp only [bAnd_iff] at h
    exact h
  unfold tableI1OK
  simp only []
  rw [e2, dat1, img1, e1]
  simp only [Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allW hk (fun j hj => (hg j hj).1) hl1 fun j hj => ?_
    rw [blk1, blkTrivOK_eq (hc j hj)]
    exact (t1' j hj).1
  · refine allW (f := fun t => commTT 1408 t (tabW wordZ)) hk (fun j hj => (hg j hj).1) hl1
      fun j hj => ?_
    rw [wZ.1, commTT_eq (hc j hj) wZ.2]
    exact (t1' j hj).2
  · refine memT_of (Nat.blt_eq.mp t3) ?_
    rw [wA.1, tblEq_eq wA.2 (hT _ (Nat.blt_eq.mp t3)), Nat.eq_of_beq_eq_true t5]
    exact Nat.beq_refl _
  · refine memT_of (Nat.blt_eq.mp t7) ?_
    rw [wZ.1, tblEq_eq wZ.2 (hT _ (Nat.blt_eq.mp t7)), Nat.eq_of_beq_eq_true t9]
    exact Nat.beq_refl _
  · unfold sqInOK pair4
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < TI1.cnt := by simpa [hRec] using hi
    have hv := allN_spec t10 i (by rw [← (headI_spec kH1).2.2.1]; exact hi')
    simp only [CFSG.KC.BfsPin.strictB_app, bAnd_iff] at hv
    obtain ⟨hq, he⟩ := hv
    have epc : pcomp 1408 11 (mask 11) (TI1.T i) (TI1.T i) = pc (TI1.T i) (TI1.T i) := rfl
    rw [← getElem!_pos _ i hi, hRec_get hi', compT_unpack (hT i hi') (hT i hi'), epc,
      Nat.eq_of_beq_eq_true he, idT_eq, wA.1, wZ.1, wAZ.1]
    unfold memT
    rw [Array.any_eq_true]
    have hq' := Nat.blt_eq.mp hq
    refine ⟨TQ1 i, by simpa using hq', ?_⟩
    match h : TQ1 i, hq' with
    | 0, _ => exact tblEq_self cId
    | 1, _ => exact tblEq_self wA.2
    | 2, _ => exact tblEq_self wZ.2
    | 3, _ => exact tblEq_self wAZ.2

theorem tI3 : tableI3OK = true := by
  obtain ⟨hk3, hg3, -, -⟩ := headI_spec kH3
  obtain ⟨hk4, hg4, -, -⟩ := kH4spec
  obtain ⟨e1, e2, hT⟩ := r3
  obtain ⟨f1, f2, hT4⟩ := r4
  have hc3 := cnW (fun j hj => (hg3 j hj).1) hl3 hk3
  have hc4 := cnW (fun j hj => (hg4 j hj).1) hl4 hk4
  have t := kT3
  simp only [bAnd_iff] at t
  obtain ⟨t1, t3, t5, t6⟩ := t
  simp only [CFSG.KC.BfsPin.strictB_app] at t6
  have t3' : ∀ j < 4, blkTrivK 1408 11 4 (TB.F 2) (TI4.GI j) = true ∧
      Nat.blt (TW3 j) TI3.cnt = true ∧ Nat.beq (TI3.T (TW3 j)) (TI4.GI j) = true := by
    intro j hj
    have h := allN_spec t3 j hj
    simp only [bAnd_iff] at h
    exact h
  unfold tableI3OK
  simp only []
  rw [e2, f2, dat3, img3, e1, f1]
  simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true']
  have hn : ∀ {X : Nat}, Cn X → (∀ i < TI3.cnt, Nat.beq (TI3.T i) X = false) →
      memT 1408 (hRec 1408 11 TI3.cnt TI3.T TI3.PL).1 (tabT (unpack 1408 11 X)) = false := by
    intro X hX h
    unfold memT
    rw [Bool.eq_false_iff, ne_eq, Array.any_eq_true]
    rintro ⟨i, hi, he⟩
    have hi' : i < TI3.cnt := by simpa [hRec] using hi
    rw [← getElem!_pos _ i hi, hRec_get hi', tblEq_eq hX (hT i hi')] at he
    have e := Nat.eq_of_beq_eq_true he
    have := h i hi'
    rw [← e, Nat.beq_refl] at this
    cases this
  have hx : ∀ i < TI3.cnt, Nat.beq (TI3.T i) (WK wordA) = false ∧
      Nat.beq (TI3.T i) (WK wordZ₁) = false ∧ Nat.beq (TI3.T i) (WK (wordA ++ wordZ₁)) = false := by
    intro i hi
    have h := allN_spec t6 i (by rw [← (headI_spec kH3).2.2.1]; exact hi)
    simp only [CFSG.KC.BfsPin.strictB_app, bAnd_iff] at h
    obtain ⟨a, b, c⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · cases e : Nat.beq (TI3.T i) (WK wordA)
      · rfl
      · rw [e] at a; cases a
    · cases e : Nat.beq (TI3.T i) (WK wordZ₁)
      · rfl
      · rw [e] at b; cases b
    · cases e : Nat.beq (TI3.T i) (WK (wordA ++ wordZ₁))
      · rfl
      · rw [e] at c; cases c
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allW (f := fun t => commTT 1408 t (tabW wordZ₁)) hk3 (fun j hj => (hg3 j hj).1) hl3
      fun j hj => ?_
    rw [wZ1.1, commTT_eq (hc3 j hj) wZ1.2]
    exact allN_spec t1 j hj
  · refine allW hk4 (fun j hj => (hg4 j hj).1) hl4 fun j hj => ?_
    rw [blk3, blkTrivOK_eq (hc4 j hj)]
    exact (t3' j hj).1
  · refine allW hk4 (fun j hj => (hg4 j hj).1) hl4 fun j hj => ?_
    obtain ⟨-, h3, h4⟩ := t3' j hj
    refine memT_of (Nat.blt_eq.mp h3) ?_
    rw [tblEq_eq (hc4 j hj) (hT _ (Nat.blt_eq.mp h3)), Nat.eq_of_beq_eq_true h4]
    exact Nat.beq_refl _
  · unfold sqOneOK
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < TI4.cnt := by simpa [hRec] using hi
    rw [← getElem!_pos _ i hi, hRec_get hi', compT_unpack (hT4 i hi') (hT4 i hi'), idT_eq,
      tblEq_eq (canonK_pcomp (hT4 i hi') (hT4 i hi')) cId]
    exact allN_spec t5 i (by rw [← kH4spec.2.2.1]; exact hi')
  · rw [wA.1]
    exact hn wA.2 fun i hi => (hx i hi).1
  · rw [wZ1.1]
    exact hn wZ1.2 fun i hi => (hx i hi).2.1
  · rw [wAZ1.1]
    exact hn wAZ1.2 fun i hi => (hx i hi).2.2

end CFSG.KD.HN1408

end
