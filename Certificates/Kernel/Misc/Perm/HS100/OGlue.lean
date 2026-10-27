module

public import Certificates.Kernel.Misc.Perm.HS100.OChecks
public import Certificates.Kernel.Misc.Perm.HS100.TGlue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.O

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of commA_F ppow_canon pw_eq)
open CertificateChecks.KernelMisc.HS100.S0 (listOf getOf cK cK_eq)
open CertificateChecks.KernelMisc.HS100.T (allN_congr)

theorem perms' : (∀ k < 16, permB 100 7 (OX.F k) = true) ∧ (∀ k < 19, permB 100 7 (FX.F k) = true) ∧
    ∀ l < 24, permB 100 7 (LK l) = true := by
  have h := perms
  simp only [Bool.and_eq_true] at h
  exact ⟨fun k hk => allN_spec h.1.1 k hk, fun k hk => allN_spec h.1.2 k hk,
    fun l hl => allN_spec h.2 l hl⟩

theorem ppO {k : ℕ} (hk : k < 16) : PP 100 7 (OX.F k) := pp_of_permB sz (perms'.1 k hk)

theorem ppF {k : ℕ} (hk : k < 19) : PP 100 7 (FX.F k) := pp_of_permB sz (perms'.2.1 k hk)

theorem ppL {l : ℕ} (hl : l < 24) : PP 100 7 (LK l) := pp_of_permB sz (perms'.2.2 l hl)

theorem o_get {k : ℕ} (hk : k < 16) : s5oTab k = unpack 100 7 (OX.F k) := by
  rw [s5oTab, OX.eq]
  exact hexTable3_sound OX.all k hk

theorem f_get {k : ℕ} (hk : k < 19) : s5fTab k = unpack 100 7 (FX.F k) := by
  rw [s5fTab, FX.eq]
  exact hexTable3_sound FX.all k hk

theorem hexAt_max2 (b : ByteArray) (o : ℕ) : ∀ d,
    CFSG.Monster.B.Max2.Native.hexAt b o d = CFSG.Monster.B.Co2.Native.hexAt b o d
  | 0 => rfl
  | d + 1 => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexAt, hexAt_max2 b o d]
    rfl

theorem k_eq {i : ℕ} (hi : i < 1024) : s5fK i = KK i := by
  have h := congrArg (·[i]!) (hexTable_sound KX.all 0 (by norm_num))
  simp only at h
  rw [CFSG.Monster.B.Co2.Native.hexTable, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn] at h
  rw [s5fK, hexAt_max2, KX.eq, KK]
  simpa using h

theorem j_eq {i : ℕ} (hi : i < 1024) : s5fJ i = JJ i := by
  have h := congrArg (·[i]!) (hexTable_sound JX.all 0 (by norm_num))
  simp only at h
  rw [CFSG.Monster.B.Co2.Native.hexTable, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn] at h
  rw [s5fJ, hexAt_max2, JX.eq, JJ]
  simpa using h

theorem nums' : OS.ng = 4 ∧ OS.N = 1024 ∧ ∀ k < 4, OS.G k = OX.F k := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, fun k hk => Nat.eq_of_beq_eq_true (allN_spec h.2 k hk)⟩

theorem sGens_get : ∀ k < 4, s5oSGens[k]! = unpack 100 7 (OX.F k) := by
  intro k hk
  interval_cases k <;> exact o_get (by norm_num)

theorem oPin : enumOK 100 s5oSGens s5Keys s5oSCert = true ∧
    s5oSCert.pts = Array.ofFn (n := OS.N) fun i => unpack 100 7 (OS.T i.val) := by
  have hs : s5oSGens.size = OS.ng := by rw [nums'.1]; rfl
  have hg : ∀ k < OS.ng, s5oSGens[k]! = unpack 100 7 (OS.G k) := fun k hk => by
    rw [nums'.1] at hk; rw [sGens_get k hk, nums'.2.2 k hk]
  have hp : ∀ k < OS.ng, permOK 100 7 (mask 7) (100 * 7) (OS.G k)
      (pinvS 100 7 (mask 7) (OS.G k)) = true := fun k hk => by
    rw [nums'.1] at hk; rw [nums'.2.2 k hk]; exact perms'.1 k (by omega)
  have hf : OS.N ≤ 2 ^ 20 := by rw [nums'.2.1]; norm_num
  exact ⟨enumOK_of_bfsK_base hs hg hp OS.ok (by decide) keys hf,
    enumBfs_pts_base hs hg OS.ok (by decide) keys hf⟩

theorem cOS : ∀ i < 1024, canonK 100 7 (mask 7) (100 * 7) (OS.T i) = true := fun i hi =>
  bfsK_canon OS.ok i (by rw [nums'.2.1]; exact hi)

theorem pt_get {i : ℕ} (hi : i < 1024) : s5oSCert.pts[i]! = unpack 100 7 (OS.T i) :=
  getOf oPin.2 i (by rw [nums'.2.1]; exact hi)

theorem hsize : s5oSCert.pts.size = 1024 := by rw [oPin.2, Array.size_ofFn, nums'.2.1]

theorem rep_lt {k : ℕ} (hk : k < 19) : s5fRep[k]! < 1024 :=
  Nat.blt_eq.mp (allN_spec reps k hk)

theorem c_get {k : ℕ} (hk : k < 19) : s5fC k = unpack 100 7 (CC k) := pt_get (rep_lt hk)

theorem xs_get {i : ℕ} (hi : i < 7) : s5oXs[i]! = unpack 100 7 (OX.F (7 + i)) := by
  rw [← o_get (by omega)]
  interval_cases i <;> rfl

theorem t_unpack {i : ℕ} (hi : i < 6) : s5fT i = unpack 100 7 (TK i) := by
  rw [s5fT, xs_get (by omega), xs_get (by omega), compA_unpack (ppO (by omega)).1 (ppO (by omega)).1,
    TK, show 7 + (i + 1) = 8 + i by omega]

theorem tk_pp {i : ℕ} (hi : i < 6) : PP 100 7 (TK i) := (ppO (by omega)).mul (ppO (by omega))

theorem g_unpack {k : ℕ} (hk : k < 12) : s5fG k = unpack 100 7 (GK k) := by
  unfold s5fG GK
  split_ifs with h
  · exact t_unpack h
  · have hs := ppO (k := 6) (by norm_num)
    rw [t_unpack (by omega), s5oS, o_get (by norm_num), conjA, invCand_PP hs,
      compA_unpack (tk_pp (by omega)).1 hs.inv.1, compA_unpack hs.1 (canonK_pcomp (tk_pp (by omega)).1
        hs.inv.1)]

theorem l_unpack {l : ℕ} (hl : l < 24) : s5fLetter l = unpack 100 7 (LK l) := by
  unfold s5fLetter LK
  split_ifs with h
  · exact g_unpack h
  · have hg : PP 100 7 (GK (l - 12)) := by
      have := ppL (l := l - 12) (by omega)
      unfold LK at this
      rwa [if_pos (by omega)] at this
    rw [g_unpack (by omega), invCand_PP hg]

theorem eval_unpack (w : List ℕ) (hw : ∀ l ∈ w, l < 24) : ∀ (acc : Array ℕ) (A : ℕ),
    canonK 100 7 (mask 7) (100 * 7) A = true → acc = unpack 100 7 A →
    w.foldl (fun acc l => compA 100 acc (s5fLetter l)) acc = unpack 100 7
      (w.foldl (fun acc l => pcomp 100 7 (mask 7) acc (LK l)) A) ∧
    canonK 100 7 (mask 7) (100 * 7) (w.foldl (fun acc l => pcomp 100 7 (mask 7) acc (LK l)) A) =
      true := by
  induction w with
  | nil => intro acc A hA e; exact ⟨e, hA⟩
  | cons l w ih =>
    intro acc A hA e
    have hl := hw l List.mem_cons_self
    simp only [List.foldl_cons]
    refine ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) _ _ (canonK_pcomp hA (ppL hl).1) ?_
    rw [e, l_unpack hl, compA_unpack hA (ppL hl).1]

theorem evalK_eq (w : List ℕ) (hw : ∀ l ∈ w, l < 24) : s5fEval w = unpack 100 7 (evalK w) :=
  (eval_unpack w hw (idA 100) (pidn 100 7) pidPP.1 hidA).1

theorem evalK_canon (w : List ℕ) (hw : ∀ l ∈ w, l < 24) :
    canonK 100 7 (mask 7) (100 * 7) (evalK w) = true :=
  (eval_unpack w hw (idA 100) (pidn 100 7) pidPP.1 hidA).2

theorem pow5_unpack {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    s5oPow5 (unpack 100 7 p) = unpack 100 7 (p5K p) := by
  have c2 := canonK_pcomp hp hp
  have c3 := canonK_pcomp hp c2
  rw [s5oPow5, compA_unpack hp hp, compA_unpack hp c2, compA_unpack hp c3,
    compA_unpack hp (canonK_pcomp hp c3), p5K]

theorem p5_canon {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    canonK 100 7 (mask 7) (100 * 7) (p5K p) = true :=
  canonK_pcomp hp (canonK_pcomp hp (canonK_pcomp hp (canonK_pcomp hp hp)))

theorem fives' {k : ℕ} (hk : k < 19) : Nat.beq (p5K (FX.F k)) (pidn 100 7) = true ∧
    Nat.beq (FX.F k) (pidn 100 7) = false ∧ cK (FX.F k) (CC k) = true := by
  have h := allN_spec fives k hk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cCC {k : ℕ} (hk : k < 19) : canonK 100 7 (mask 7) (100 * 7) (CC k) = true := cOS _ (rep_lt hk)

theorem invPt_eq {i : ℕ} (hi : i < 1024) :
    (!s5fIsInv s5oSCert.pts[i]! || eqA 100 s5oSCert.pts[i]! (idA 100) ||
      (decide (s5fK i < s5fRep.size) && decide (s5fJ i < s5oSCert.pts.size) &&
        eqA 100 (compA 100 s5oSCert.pts[s5fJ i]! (s5fC (s5fK i)))
          (compA 100 s5oSCert.pts[i]! s5oSCert.pts[s5fJ i]!))) = invPt i := by
  have c := cOS i hi
  unfold invPt
  rw [CFSG.KC.ConjOrb.strictB_eq, pt_get hi, s5fIsInv, compA_unpack c c, hidA,
    eqA_F (canonK_pcomp c c) pidPP.1, eqA_F c pidPP.1, k_eq hi, j_eq hi, hsize]
  have hrs : s5fRep.size = 19 := rfl
  have db : ∀ a b : ℕ, decide (a < b) = Nat.blt a b := fun a b =>
    Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, Nat.blt_eq])
  rw [hrs, db, db]
  congr 1
  cases h : (Nat.blt (KK i) 19 && Nat.blt (JJ i) 1024)
  · rw [Bool.false_and, Bool.false_and]
  · rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
    have cJ := cOS _ h.2
    have cK' := cCC h.1
    rw [pt_get h.2, c_get h.1, compA_unpack cJ cK', compA_unpack c cJ,
      eqA_F (canonK_pcomp cJ cK') (canonK_pcomp c cJ)]

theorem s5fOK_true : s5fOK = true := by
  have h2 : allLt s5fRep.size (fun k => decide (s5fRep[k]! < s5oSCert.pts.size)) = true := by
    rw [allLt_iff]
    intro k hk
    rw [hsize]
    exact decide_eq_true (rep_lt hk)
  have h3 : allLt s5fRep.size (fun k => validA 100 (s5fTab k) && s5InP (s5fTab k) &&
      eqA 100 (s5oPow5 (s5fTab k)) (idA 100) && !eqA 100 (s5fTab k) (idA 100) &&
      eqA 100 (compA 100 (s5fTab k) (s5fC k)) (compA 100 (s5fC k) (s5fTab k))) = true := by
    rw [allLt_iff]
    intro k hk
    have hk' : k < 19 := hk
    have f := fives' hk'
    have cF := (ppF hk').1
    rw [f_get hk', c_get hk', validA_unpack (perms'.2.1 k hk'),
      s5InP_unpack (allN_spec fsift k hk'), pow5_unpack cF, hidA, eqA_F (p5_canon cF) pidPP.1,
      eqA_F cF pidPP.1, ← commA, cK_eq cF (cCC hk'), f.1, f.2.1, f.2.2]
    rfl
  have h4 : allLt s5oSCert.pts.size (fun i =>
      !s5fIsInv s5oSCert.pts[i]! || eqA 100 s5oSCert.pts[i]! (idA 100) ||
        (decide (s5fK i < s5fRep.size) && decide (s5fJ i < s5oSCert.pts.size) &&
          eqA 100 (compA 100 s5oSCert.pts[s5fJ i]! (s5fC (s5fK i)))
            (compA 100 s5oSCert.pts[i]! s5oSCert.pts[s5fJ i]!))) = true := by
    rw [allLt_iff]
    intro i hi
    rw [hsize] at hi
    rw [invPt_eq hi]
    exact allN_spec invs i hi
  have h5 : allLt 7 (fun i => validA 100 s5oXs[i]!) = true := by
    rw [allLt_iff]
    intro i hi
    rw [xs_get hi]
    exact validA_unpack (perms'.1 _ (by omega))
  have h6 : validA 100 s5oS = true := by
    rw [s5oS, o_get (by norm_num)]; exact validA_unpack (perms'.1 6 (by norm_num))
  have h7 : allLt 24 (fun l => validA 100 (s5fLetter l)) = true := by
    rw [allLt_iff]
    intro l hl
    rw [l_unpack hl]
    exact validA_unpack (perms'.2.2 l hl)
  have hA : ∀ l ∈ s5fWA, l < 24 := by decide
  have hB : ∀ l ∈ s5fWB, l < 24 := by decide
  have hw := words
  simp only [Bool.and_eq_true] at hw
  have h8 : eqA 100 (s5fEval s5fWA) (hs100Arr 0) = true := by
    rw [evalK_eq _ hA, hs100Arr_eq 0 (by norm_num), eqA_F (evalK_canon _ hA)
      (CertificateChecks.KernelMisc.HS100.Clique.cA)]
    exact hw.1
  have h9 : eqA 100 (s5fEval s5fWB) (hs100Arr 1) = true := by
    rw [evalK_eq _ hB, hs100Arr_eq 1 (by norm_num), eqA_F (evalK_canon _ hB)
      (CertificateChecks.KernelMisc.HS100.Clique.canonG (k := 1) (by norm_num) |>
        fun h => by rwa [CertificateChecks.KernelMisc.HS100.Clique.nums'.2.2.2.1] at h)]
    exact hw.2
  have hAl : (s5fWA.all fun l => decide (l < 24)) = true := by decide
  have hBl : (s5fWB.all fun l => decide (l < 24)) = true := by decide
  unfold s5fOK
  rw [oPin.1, h2, h3, h4, h5, h6, h7, hAl, hBl, h8, h9]
  rfl

end CertificateChecks.KernelMisc.HS100.O

end
