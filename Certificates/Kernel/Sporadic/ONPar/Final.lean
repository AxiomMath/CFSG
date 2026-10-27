module

public import Certificates.Kernel.Sporadic.ONPar.Checks
public import Certificates.Kernel.Sporadic.ONPar.ChecksE
public import Certificates.Kernel.Sporadic.ON8.Lin
public import Certificates.Kernel.Sporadic.ON3.Final
public import Certificates.Kernel.Sporadic.OddCore.ON2129F
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
public meta import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.ONPar.Neg
import Certificates.Kernel.Sporadic.ONPar.NegE

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONPar.cgAll CertificateChecks.KernelSpor.ONPar.cgOK 8
#kon_join CertificateChecks.KernelSpor.ONPar.oAll CertificateChecks.KernelSpor.ONPar.oEnumOK 3

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONLin CFSG.KS.TW CFSG.KS.PW CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.KC.BfsPin
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore
open CFSG.Sporadic.ON.Native (nPts)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CertificateChecks.KernelSpor.ON (TT UU)
open CertificateChecks.KernelSpor.ON3 (ZT QT DT mG bposK blkK)

abbrev Rd (a : Array Nat) (F : Nat → Nat) : Prop := ∀ x < 245520, a[x]! = F x ∧ F x < 245520

theorem rd_word {w : List Int} (hw : ON3.Let7 w) : Rd (wordArr w) (wK w) :=
  fun _ hx => ON3.wordArr_get hw hx

theorem rd_pc {a b : Array Nat} {F G : Nat → Nat} (ha : Rd a F) (hb : Rd b G) :
    Rd (pcomp nPts a b) fun x => F (G x) := fun x hx => by
  rw [pcomp_get' (n := nPts) hx, (hb x hx).1]
  exact ha _ (hb x hx).2

theorem rd_pid : Rd (pid nPts) fun x => x := fun _ hx => ⟨pid_get' hx, hx⟩

theorem peq_rd {a b : Array Nat} {F G : Nat → Nat} (ha : Rd a F) (hb : Rd b G)
    (h : ∀ x < 245520, F x = G x) : peq nPts a b = true :=
  ON3.peq_of' fun x hx => by rw [(ha x hx).1, (hb x hx).1, h x hx]

theorem let_v : ON3.Let7 onpVWord := by unfold ON3.Let7 onpVWord; decide
theorem let_x : ON3.Let7 onpXWord := by unfold ON3.Let7 onpXWord; decide
theorem let_m : ON3.Let7 onpMWord := by unfold ON3.Let7 onpMWord; decide
theorem let_n : ON3.Let7 onpNWord := by unfold ON3.Let7 onpNWord; decide

theorem rd_v : Rd onpVArr vK := rd_word let_v
theorem rd_x : Rd onpXArr xK := rd_word let_x
theorem rd_m : Rd onpMArr mK := rd_word let_m
theorem rd_n : Rd onpNArr nK := rd_word let_n
theorem rd_g : Rd onpGArr gK := (rd_pc rd_n (rd_pc rd_x (rd_pc rd_m rd_x)) :)

theorem lin_vK : ON8.L vK := ON8.lin_word7 let_v
theorem lin_xK : ON8.L xK := ON8.lin_word7 let_x
theorem lin_mK : ON8.L mK := ON8.lin_word7 let_m
theorem lin_nK : ON8.L nK := ON8.lin_word7 let_n
theorem lin_gK : ON8.L gK := (Lin.comp lin_nK (Lin.comp lin_xK (Lin.comp lin_mK lin_xK)) :)

theorem c_restrict : restrictOK onpVArr Data.TPoints onpV32 = true := by
  have hR := ON3.all_range ON3.r_points
  have h := r_ok
  unfold rOK at h
  have hsz : Data.TPoints.size = 32 := rfl
  unfold restrictOK
  refine ON3.allBelowN_iff.2 fun k hk => ?_
  have hk' : k < 32 := hk
  have hlt : Data.TPoints[k]! < 245520 := by
    have := hR k hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have h2 := allN_spec h k hk'
  rw [bAnd_iff] at h2
  rw [(rd_v _ hlt).1, hsz, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem part1 : memIn TStrong Data.TChain.base onpVArr = true ∧
    restrictOK onpVArr Data.TPoints onpV32 = true ∧
    blockImgOK onpVArr Data.quotientBlocks onpVB = true ∧
    peq nPts (pcomp nPts onpXArr zArr) (pcomp nPts (pcomp nPts onpVArr zArr) onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr onpVArr) (pcomp nPts zArr onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr (pcomp nPts onpXArr onpXArr)) (pid nPts) = true ∧
    memIn MStrong Data.MChain.base onpMArr = true ∧
    memIn MStrong Data.MChain.base onpNArr = true ∧
    peq nPts (pcomp nPts onpGArr zArr) (pcomp nPts tArr onpGArr) = true ∧
    peq nPts (pcomp nPts qArr qArr) zArr = true :=
  ⟨ON3.memT (G := vK) (fun _ hk => (rd_v _ (ON3.bB_lt hk)).1) (fun _ hk => (rd_v _ (ON3.bB_lt hk)).2)
      v_sift,
    c_restrict,
    ON3.blockImg_of (G := vK) (fun y hy => (rd_v y hy).1) b_ok,
    peq_rd (rd_pc rd_x ON3.z_get) (rd_pc (rd_pc rd_v ON3.z_get) rd_x)
      (ON8.agree (Lin.comp lin_xK ON8.lin_ZT) (Lin.comp lin_vK (Lin.comp ON8.lin_ZT lin_xK)) rel1_ok),
    peq_rd (rd_pc rd_x rd_v) (rd_pc ON3.z_get rd_x)
      (ON8.agree (Lin.comp lin_xK lin_vK) (Lin.comp ON8.lin_ZT lin_xK) rel2_ok),
    peq_rd (rd_pc rd_x (rd_pc rd_x rd_x)) rd_pid
      (ON8.agree (Lin.comp lin_xK (Lin.comp lin_xK lin_xK)) Lin.id rel3_ok),
    ON3.memM (G := mK) (fun _ hk => (rd_m _ (ON3.bB_lt hk)).1) (fun _ hk => (rd_m _ (ON3.bB_lt hk)).2)
      m_sift,
    ON3.memM (G := nK) (fun _ hk => (rd_n _ (ON3.bB_lt hk)).1) (fun _ hk => (rd_n _ (ON3.bB_lt hk)).2)
      n_sift,
    peq_rd (rd_pc rd_g ON3.z_get) (rd_pc ON3.t_get rd_g)
      (ON8.agree (Lin.comp lin_gK ON8.lin_ZT) (Lin.comp (ON8.lin_DT (j := 0) (by norm_num)) lin_gK)
        rel4_ok),
    peq_rd (rd_pc ON3.q_get ON3.q_get) ON3.z_get
      (ON8.agree (Lin.comp ON8.lin_QT ON8.lin_QT) ON8.lin_ZT rel5_ok)⟩

theorem om_tabs : omegaEnum.tabs.size = 8 ∧ ∀ i < 8, omegaEnum.tabs[i]! = unpack 32 6 (OME.T i) ∧
    canonK 32 6 (mask 6) (32 * 6) (OME.T i) = true := by
  rw [ON2129.omegaEnum_eq.1]
  refine ⟨by simp [penumRec]; rfl, fun i hi => ⟨ON2129.rec_get (cnt := OME.cnt) hi,
    penumPt_canon (ON2129.om_pt (i := i) hi)⟩⟩

theorem t_tabs : t32Enum.tabs.size = 512 ∧ ∀ i < 512, t32Enum.tabs[i]! = unpack 32 6 (T32E.T i) ∧
    canonK 32 6 (mask 6) (32 * 6) (T32E.T i) = true := by
  rw [ON2129.t32Enum_eq]
  refine ⟨by simp [penumRec]; rfl, fun i hi => ⟨ON2129.rec_get (cnt := T32E.cnt) hi,
    penumPt_canon (ON2129.t32_pt (i := i) hi)⟩⟩

theorem om_sq : ∀ a < 8, pcomp 32 6 (mask 6) (OME.T a) (OME.T a) = pidn 32 6 := by
  have h := ON2129.om_facts
  simp only [bAnd_iff] at h
  exact fun a ha => Nat.eq_of_beq_eq_true (allN_spec h.2.1 a ha)

theorem tinv_parts : ∀ j < 512, nget tInv j < 512 ∧
    pcomp 32 6 (mask 6) (T32E.T (nget tInv j)) (T32E.T j) = pidn 32 6 := by
  have h := tinv_ok
  unfold tInvOK at h
  rw [bAnd_iff] at h
  intro j hj
  have h2 := allN_spec h.2 j hj
  rw [strictB_app', bAnd_iff] at h2
  exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem om_inv : (∀ k < 8, onpOmInv[k]! = unpack 32 6 (OME.T k)) ∧
    invsOK 32 omegaEnum.tabs onpOmInv = true :=
  CFSG.KC.L34KSnd.invsOK_of_pcomp (G := OME.T) (GI := OME.T) om_tabs.1
    (fun k hk => (om_tabs.2 k hk).1) fun k hk =>
      ⟨(om_tabs.2 k hk).2, (om_tabs.2 k hk).2, om_sq k hk⟩

theorem t_inv : (∀ k < 512, onpTInv[k]! = unpack 32 6 (T32E.T (nget tInv k))) ∧
    invsOK 32 t32Enum.tabs onpTInv = true :=
  CFSG.KC.L34KSnd.invsOK_of_pcomp (G := T32E.T) (GI := fun k => T32E.T (nget tInv k)) t_tabs.1
    (fun k hk => (t_tabs.2 k hk).1) fun k hk =>
      ⟨(t_tabs.2 k hk).2, (t_tabs.2 _ (tinv_parts k hk).1).2,
        CFSG.KC.L34KSnd.pcomp_inv_of_pcomp (t_tabs.2 _ (tinv_parts k hk).1).2 (t_tabs.2 k hk).2
          (tinv_parts k hk).2⟩

theorem cg_parts {s j : Nat} (hs : s < 8) (hj : j < 512) :
    ONPC.G (512 * s + j) = pcomp 32 6 (mask 6) (pcomp 32 6 (mask 6)
      (pcomp 32 6 (mask 6) (OME.T s) (T32E.T j)) (OME.T s)) (T32E.T (nget tInv j)) ∧
    canonK 32 6 (mask 6) (32 * 6) (ONPC.G (512 * s + j)) = true := by
  have h := cgAll s hs
  unfold cgOK at h
  have h2 := allN_spec h j hj
  rw [strictB_app', strictB_app', strictB_app', bAnd_iff] at h2
  have e : Nat.add (Nat.mul s 512) j = 512 * s + j := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, h2.2⟩

theorem comm_size : onpCommGens.size = 4096 := by
  unfold onpCommGens
  rw [Array.size_ofFn, om_tabs.1, t_tabs.1]

theorem comm_get {k : Nat} (hk : k < 4096) : onpCommGens[k]! = unpack 32 6 (ONPC.G k) := by
  have hs : k / 512 < 8 := by omega
  have hj : k % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have e : onpCommGens[k]! = commTab 32 omegaEnum.tabs[k / 512]! t32Enum.tabs[k % 512]!
      onpOmInv[k / 512]! onpTInv[k % 512]! := by
    rw [getElem!_pos _ k (by rw [comm_size]; exact hk)]
    unfold onpCommGens
    rw [Array.getElem_ofFn]
    simp only [t_tabs.1]
  have ca := (om_tabs.2 _ hs).2
  have cb := (t_tabs.2 _ hj).2
  have cc := (t_tabs.2 _ (tinv_parts _ hj).1).2
  rw [e, (om_tabs.2 _ hs).1, (t_tabs.2 _ hj).1, om_inv.1 _ hs, t_inv.1 _ hj]
  unfold commTab
  rw [CFSG.KC.L34KSnd.comp_unpack' ca cb, CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp ca cb) ca,
    CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp (canonK_pcomp ca cb) ca) cc]
  have g := (cg_parts hs hj).1
  rw [Nat.div_add_mod] at g
  exact congrArg (unpack 32 6) g.symm

theorem comm_gens : GensOK 32 6 ONPC.k ONPC.G onpCommGens := by
  have hk : ONPC.k = 4096 := rfl
  refine ⟨by rw [comm_size, hk], fun j hj => ?_⟩
  rw [hk] at hj
  refine ⟨comm_get hj, ?_⟩
  have hs : j / 512 < 8 := by omega
  have := (cg_parts hs (Nat.mod_lt j (by norm_num))).2
  rwa [Nat.div_add_mod] at this

theorem c_parts : penumHdK (pidn 32 6) ONPC.cnt 16 ONPC.T ONPC.PL = true ∧
    (∀ i < ONPC.cnt, penumPtK 32 6 (mask 6) (32 * 6) false ONPC.G ONPC.GI ONPC.k ONPC.cnt ONPC.T
      ONPC.PL ONPC.POS ONPC.SRT ONPC.SRI i = true) ∧
    (∀ i < ONPC.cnt, inFour (ONPC.T i) = true) ∧ inC (pk 0) = true ∧ inC (pk 1) = true := by
  have h := cenum_ok
  unfold cEnumOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, hh, hs, h4, h0, h1⟩ := h
  have hcnt : ONPC.cnt ≤ 16 := by
    have hh' := hh
    unfold penumHdK at hh'
    simp only [bAnd_iff] at hh'
    exact Nat.le_of_ble_eq_true hh'.2.1
  exact ⟨hh, fun i hi => penumSl_spec hs i (Nat.zero_le _) (by omega) hi, allN_spec h4, h0, h1⟩

theorem c_enum : onpCommEnum = penumRec 32 6 ONPC.cnt ONPC.T ONPC.PL ∧
    enumOK 32 onpCommGens (penumRec 32 6 ONPC.cnt ONPC.T ONPC.PL) = true :=
  penumK_left_sound (cap := 16) ON2129.szOK32 comm_gens c_parts.1 c_parts.2.1

theorem b_parts : Data.T32z = unpack 32 6 (pk 0) ∧ canonK 32 6 (mask 6) (32 * 6) (pk 0) = true ∧
    onpV32 = unpack 32 6 (pk 1) ∧ canonK 32 6 (mask 6) (32 * 6) (pk 1) = true ∧
    Data.quotientConjugator = unpack 120 7 (pk 2) ∧ canonK 120 7 (mask 7) (120 * 7) (pk 2) = true ∧
    canonK 120 7 (mask 7) (120 * 7) (pk 3) = true ∧
    pcomp 120 7 (mask 7) (pk 3) (pk 2) = pidn 120 7 ∧
    onpVB = unpack 120 7 (pk 4) ∧ canonK 120 7 (mask 7) (120 * 7) (pk 4) = true ∧
    ∀ j < 3, blkK (mG j) (mbK j) = true ∧ canonK 120 7 (mask 7) (120 * 7) (pk (5 + j)) = true ∧
      ∀ b < 120, mbK j b = pg 7 (mask 7) (pk (5 + j)) b := by
  have h := bind_ok
  unfold bindOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨unpack_eq_of_bindArrK a1, a2, unpack_eq_of_bindArrK a3, a4, unpack_eq_of_bindArrK a5, a6,
    a7, Nat.eq_of_beq_eq_true a8, unpack_eq_of_bindArrK a9, a10, fun j hj => ?_⟩
  have h := allN_spec a11 j hj
  rw [strictB_app'] at h
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, fun b hb => Nat.eq_of_beq_eq_true (allN_spec h.2.2 b hb)⟩

theorem szOK120 : szOK 120 7 = true := CFSG.KC.L34KSnd.canon_sz b_parts.2.2.2.2.2.1

theorem uinv : pinvCand 120 Data.quotientConjugator = unpack 120 7 (pk 3) := by
  obtain ⟨-, -, -, -, hu, c2, c3, e32, -⟩ := b_parts
  rw [hu]
  exact CFSG.KC.L34KSnd.invTab_eq_of_pcomp c2 c3 (CFSG.KC.L34KSnd.pcomp_inv_of_pcomp c3 c2 e32)

theorem conj_unpack {g x gi : Nat} (hg : canonK 120 7 (mask 7) (120 * 7) g = true)
    (hx : canonK 120 7 (mask 7) (120 * 7) x = true)
    (hgi : canonK 120 7 (mask 7) (120 * 7) gi = true) :
    conjTab 120 (unpack 120 7 g) (unpack 120 7 gi) (unpack 120 7 x) =
      unpack 120 7 (pcomp 120 7 (mask 7) (pcomp 120 7 (mask 7) g x) gi) := by
  unfold conjTab
  rw [CFSG.KC.L34KSnd.comp_unpack' hg hx, CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp hg hx) hgi]

theorem mb_tab {j : Nat} (hj : j < 3) :
    bTab (wordArrs Data.MWords)[j]! = unpack 120 7 (pk (5 + j)) := by
  obtain ⟨hb, -, hp⟩ := b_parts.2.2.2.2.2.2.2.2.2.2 j hj
  rw [(ON3.blockTab_of (fun y hy => (ON3.m_get hj y hy).1) hb).2]
  unfold unpack
  congr 1
  funext b
  exact hp b.val b.isLt

theorem og_parts : ONPO.k = 3 ∧
    ONPO.R = pcomp 120 7 (mask 7) (pcomp 120 7 (mask 7) (pk 2) (pk 4)) (pk 3) ∧
    ∀ j < 3, ONPO.G j = pcomp 120 7 (mask 7) (pcomp 120 7 (mask 7) (pk 2) (pk (5 + j))) (pk 3) ∧
      canonK 120 7 (mask 7) (120 * 7) (ONPO.G j) = true ∧
      canonK 120 7 (mask 7) (120 * 7) (ONPO.GI j) = true ∧
      pcomp 120 7 (mask 7) (ONPO.GI j) (ONPO.G j) = pidn 120 7 := by
  have h := ogen_ok
  unfold oGenOK at h
  simp only [bAnd_iff] at h
  obtain ⟨a, b, c⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, fun j hj => ?_⟩
  have h := allN_spec c j hj
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem rg_size : onpRGens.size = 3 := by
  unfold onpRGens
  rw [Array.size_map, wordArrs, pwords_eq, Array.size_map]
  rfl

theorem rg_get {j : Nat} (hj : j < 3) : onpRGens[j]! = unpack 120 7 (ONPO.G j) := by
  obtain ⟨-, -, -, -, hu, c2, c3, -, -, -, hm⟩ := b_parts
  have hj' : j < (wordArrs Data.MWords).size := by
    rw [wordArrs, pwords_eq, Array.size_map]
    exact hj
  unfold onpRGens
  rw [getElem!_pos _ j (by rw [Array.size_map]; exact hj'), Array.getElem_map,
    ← getElem!_pos _ j hj', mb_tab hj, uinv, hu, conj_unpack c2 (hm j hj).2.1 c3]
  exact congrArg (unpack 120 7) (og_parts.2.2 j hj).1.symm

theorem rgi_parts : (∀ k < 3, onpRGensInv[k]! = unpack 120 7 (ONPO.GI k)) ∧
    invsOK 120 onpRGens onpRGensInv = true :=
  CFSG.KC.L34KSnd.invsOK_of_pcomp (G := ONPO.G) (GI := ONPO.GI) rg_size (fun k hk => rg_get hk)
    fun k hk => ⟨(og_parts.2.2 k hk).2.1, (og_parts.2.2 k hk).2.2.1,
      CFSG.KC.L34KSnd.pcomp_inv_of_pcomp (og_parts.2.2 k hk).2.2.1 (og_parts.2.2 k hk).2.1
        (og_parts.2.2 k hk).2.2.2⟩

theorem rg_gens : GensOK 120 7 ONPO.k ONPO.G onpRGens := by
  refine ⟨by rw [rg_size, og_parts.1], fun j hj => ?_⟩
  rw [og_parts.1] at hj
  exact ⟨rg_get hj, (og_parts.2.2 j hj).2.1⟩

theorem rgi_gens : GensOK 120 7 ONPO.k ONPO.GI onpRGensInv := by
  refine ⟨by unfold onpRGensInv; rw [Array.size_map, rg_size, og_parts.1], fun j hj => ?_⟩
  rw [og_parts.1] at hj
  exact ⟨rgi_parts.1 j hj, (og_parts.2.2 j hj).2.2.1⟩

theorem vbar_eq : onpVBar = unpack 120 7 ONPO.R := by
  obtain ⟨-, -, -, -, hu, c2, c3, -, hvb, c4, -⟩ := b_parts
  unfold onpVBar
  rw [uinv, hu, hvb, conj_unpack c2 c4 c3]
  exact congrArg (unpack 120 7) og_parts.2.1.symm

theorem o_hd : ONPO.cnt = 315 ∧ penumHdK ONPO.R ONPO.cnt 400 ONPO.T ONPO.PL = true := by
  have h := ohd_ok
  unfold oHdOK at h
  rw [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩

theorem o_pt : ∀ i < ONPO.cnt, penumPtK 120 7 (mask 7) (120 * 7) true ONPO.G ONPO.GI ONPO.k
    ONPO.cnt ONPO.T ONPO.PL ONPO.POS ONPO.SRT ONPO.SRI i = true := by
  intro i hi
  have hs : i / 105 < 3 := by
    rw [o_hd.1] at hi
    omega
  have h := oAll _ hs
  unfold oEnumOK at h
  exact penumSl_spec h i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem o_orbit : onpROrbit = penumRec 120 7 ONPO.cnt ONPO.T ONPO.PL ∧
    treeOK (conjStep 120 onpRGens onpRGensInv) onpRGens.size onpVBar
      (penumRec 120 7 ONPO.cnt ONPO.T ONPO.PL) = true :=
  penumK_conj_sound (cap := 400) szOK120 rg_gens rgi_gens vbar_eq o_hd.2 o_pt

theorem four_ok : onpCommEnum.tabs.all (fun t => t == idTab 32 || t == Data.T32z || t == onpV32 ||
    t == comp 32 Data.T32z onpV32) = true := by
  obtain ⟨hz, cz, hv, cv, -⟩ := b_parts
  rw [c_enum.1, Array.all_eq_true]
  intro i hi
  have hi' : i < ONPC.cnt := by simpa [penumRec] using hi
  have ct := penumPt_canon (c_parts.2.1 i hi')
  have hf := c_parts.2.2.1 i hi'
  simp only [penumRec, Array.getElem_ofFn]
  rw [ON2129.idTab_eq, hz, hv, CFSG.KC.L34KSnd.comp_unpack' cz cv,
    CFSG.KS.PEnum.beq_unpack ct ON2129.idCanon.1, CFSG.KS.PEnum.beq_unpack ct cz,
    CFSG.KS.PEnum.beq_unpack ct cv, CFSG.KS.PEnum.beq_unpack ct (canonK_pcomp cz cv)]
  unfold inFour c32 at hf
  revert hf
  cases Nat.beq (ONPC.T i) (pidn 32 6) <;> cases Nat.beq (ONPC.T i) (pk 0) <;>
    cases Nat.beq (ONPC.T i) (pk 1) <;>
    cases Nat.beq (ONPC.T i) (pcomp 32 6 (mask 6) (pk 0) (pk 1)) <;> decide

theorem any_of {t : Nat} (h : inC t = true) {A : Tab} (hA : A = unpack 32 6 t) :
    onpCommEnum.tabs.any (fun x => x == A) = true := by
  obtain ⟨i, hi, e⟩ := ON3.anyN_spec (q := fun i => Nat.beq (ONPC.T i) t) (m := ONPC.cnt) h
  rw [c_enum.1, Array.any_eq_true]
  refine ⟨i, by simp [penumRec]; exact hi, ?_⟩
  simp only [penumRec, Array.getElem_ofFn]
  rw [Nat.eq_of_beq_eq_true e, hA, beq_self_eq_true]

theorem part2 : invsOK 32 omegaEnum.tabs onpOmInv = true ∧
    invsOK 32 t32Enum.tabs onpTInv = true ∧
    enumOK 32 onpCommGens onpCommEnum = true ∧
    onpCommEnum.tabs.all (fun t => t == idTab 32 || t == Data.T32z || t == onpV32 ||
      t == comp 32 Data.T32z onpV32) = true ∧
    onpCommEnum.tabs.any (fun t => t == Data.T32z) = true ∧
    onpCommEnum.tabs.any (fun t => t == onpV32) = true ∧
    orbitOK 120 onpRGens onpRGensInv onpVBar onpROrbit = true ∧
    onpROrbit.tabs.size = 315 := by
  refine ⟨om_inv.2, t_inv.2, by rw [c_enum.1]; exact c_enum.2, four_ok,
    any_of c_parts.2.2.2.1 b_parts.1, any_of c_parts.2.2.2.2 b_parts.2.2.1, ?_, ?_⟩
  · unfold orbitOK
    rw [Bool.and_eq_true, o_orbit.1]
    exact ⟨rgi_parts.2, o_orbit.2⟩
  · rw [o_orbit.1]
    simp only [penumRec, Array.size_ofFn]
    exact o_hd.1

open Certificates in
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore in
open CFSG.Sporadic.ON.Native (nPts) in
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar in
theorem facts : memIn TStrong Data.TChain.base onpVArr = true ∧
    restrictOK onpVArr Data.TPoints onpV32 = true ∧
    blockImgOK onpVArr Data.quotientBlocks onpVB = true ∧
    peq nPts (pcomp nPts onpXArr zArr) (pcomp nPts (pcomp nPts onpVArr zArr) onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr onpVArr) (pcomp nPts zArr onpXArr) = true ∧
    peq nPts (pcomp nPts onpXArr (pcomp nPts onpXArr onpXArr)) (pid nPts) = true ∧
    memIn MStrong Data.MChain.base onpMArr = true ∧
    memIn MStrong Data.MChain.base onpNArr = true ∧
    peq nPts (pcomp nPts onpGArr zArr) (pcomp nPts tArr onpGArr) = true ∧
    peq nPts (pcomp nPts qArr qArr) zArr = true ∧
    invsOK 32 omegaEnum.tabs onpOmInv = true ∧
    invsOK 32 t32Enum.tabs onpTInv = true ∧
    enumOK 32 onpCommGens onpCommEnum = true ∧
    onpCommEnum.tabs.all (fun t => t == idTab 32 || t == Data.T32z || t == onpV32 ||
      t == comp 32 Data.T32z onpV32) = true ∧
    onpCommEnum.tabs.any (fun t => t == Data.T32z) = true ∧
    onpCommEnum.tabs.any (fun t => t == onpV32) = true ∧
    orbitOK 120 onpRGens onpRGensInv onpVBar onpROrbit = true ∧
    onpROrbit.tabs.size = 315 :=
  ⟨part1.1, part1.2.1, part1.2.2.1, part1.2.2.2.1, part1.2.2.2.2.1, part1.2.2.2.2.2.1,
    part1.2.2.2.2.2.2.1, part1.2.2.2.2.2.2.2.1, part1.2.2.2.2.2.2.2.2.1, part1.2.2.2.2.2.2.2.2.2,
    part2⟩

end CertificateChecks.KernelSpor.ONPar

end
