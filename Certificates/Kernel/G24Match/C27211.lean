module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelMatch
public import Certificates.Kernel.G24Match.Chk27211
public import Certificates.Kernel.G24Tri.C27206
public import CFSG.Certificates.Kernel.G24KeySound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.Match27211

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Key CFSG.KC.DigitScan
  CFSG.EvenSporadicStandard.G24Model CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CertificateChecks.KernelG24.Tri27206

@[expose] noncomputable def L : List Nat := CFSG.KC.Co1BPair.numsOf CertificateChecks.EvenSporG24.G24T.chars

theorem tbl_eq' : tbl = L.toArray := by
  have h : tbl = parseNums CertificateChecks.EvenSporG24.g24Text := rfl
  rw [h, CertificateChecks.EvenSporG24.G24T.eq]
  exact CertificateChecks.EvenSporG24.parseNums_ofList _ (scanK_sound kText).1

theorem L_len : L.length = 27718 := (scanK_sound kText).2.1

theorem hv {i : Nat} (hi : i < 27718) : f27211 i (L.getD i 0) = true := (scanK_sound kText).2.2 i hi

theorem tbl_getD (i : Nat) : tbl.getD i 0 = L.getD i 0 := by
  rw [tbl_eq']
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem can {j : Nat} (hj : j < 16) : canonK 1365 11 (mask 11) (1365 * 11) (PG j) = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 kCan j hj

theorem ap_lt {j : Nat} (hj : j < 16) {k : Nat} (hk : k < 1365) : ap (PG j) k < 1365 := by
  exact (CFSG.KS.PF.canon_facts (can hj)).2.2.2 k hk

theorem m11_bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem m11_strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem f_spec {i v : Nat} (h : f27211 i v = true) :
    (5866 ≤ i → i < 27706 → v = ap (PG ((i - 5866) / 1365)) ((i - 5866) % 1365)) ∧
      (27706 ≤ i → v = Nat.land (Nat.shiftRight wdN (4 * (i - 27706))) 15) := by
  unfold f27211 at h
  simp only [m11_bIf_eq, m11_strictB_eq, Nat.blt_eq] at h
  refine ⟨fun h1 h2 => ?_, fun h1 => ?_⟩
  · rw [if_neg (by omega), if_pos h2] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [if_neg (by omega), if_neg (by omega)] at h
    exact Nat.eq_of_beq_eq_true h

theorem pg_val {j k : Nat} (hj : j < 16) (hk : k < 1365) :
    L.getD (5866 + 1365 * j + k) 0 = ap (PG j) k := by
  have h := (f_spec (hv (i := 5866 + 1365 * j + k) (by omega))).1 (by omega) (by omega)
  have e2 : (5866 + 1365 * j + k - 5866) / 1365 = j := by omega
  have e3 : (5866 + 1365 * j + k - 5866) % 1365 = k := by omega
  rw [e2, e3] at h
  exact h

theorem word_val {t : Nat} (ht : t < 12) :
    L.getD (27706 + t) 0 = Nat.land (Nat.shiftRight wdN (4 * t)) 15 := by
  have h := (f_spec (hv (i := 27706 + t) (by omega))).2 (by omega)
  rw [show 27706 + t - 27706 = t by omega] at h
  exact h

theorem pgNum_eq {j k : Nat} (hj : j < 16) (hk : k < 1365) : pgNum j k = ap (PG j) k := by
  unfold pgNum
  rw [tbl_getD]
  have e : 2 * nLines + 16 * 196 + nLines * j + k = 5866 + 1365 * j + k := by
    change 2 * 1365 + 16 * 196 + 1365 * j + k = _
    omega
  rw [e, pg_val hj hk]
  exact Nat.mod_eq_of_lt (ap_lt hj hk)

theorem pgArrs_get {j : Nat} (hj : j < 16) : pgArrs[j]! = unpack 1365 11 (PG j) := by
  unfold pgArrs
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_ofFn]
  unfold unpack
  congr 1
  funext k
  exact pgNum_eq hj k.2

theorem take5 (M : List Nat) (h : 5 ≤ M.length) :
    M.take 5 = [M.getD 0 0, M.getD 1 0, M.getD 2 0, M.getD 3 0, M.getD 4 0] := by
  rcases M with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, r⟩⟩⟩⟩⟩ <;> simp at h ⊢

theorem extract5 (a : Nat) (h : a + 6 ≤ L.length) :
    (tbl.extract (a + 1) (a + 6)).toList =
      [L.getD (a + 1) 0, L.getD (a + 2) 0, L.getD (a + 3) 0, L.getD (a + 4) 0, L.getD (a + 5) 0] := by
  rw [tbl_eq', List.extract_toArray, List.toList_toArray, List.extract_eq_drop_take,
    show a + 6 - (a + 1) = 5 by omega, take5 _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm, Nat.add_left_comm]

theorem waLen_eq : waLen = 5 := by
  unfold waLen
  rw [tbl_getD, show wordOffset = 27706 + 0 from rfl, word_val (by norm_num)]
  rfl

theorem wbLen_eq : wbLen = 5 := by
  unfold wbLen
  rw [tbl_getD, waLen_eq, show wordOffset + 1 + 5 = 27706 + 6 from rfl, word_val (by norm_num)]
  rfl

theorem wa_eq : waWord = [5, 1, 5, 1, 5] := by
  unfold waWord
  rw [waLen_eq, show wordOffset + 1 + 5 = 27706 + 6 from rfl, show wordOffset + 1 = 27706 + 1 from rfl,
    extract5 27706 (by simp [L_len]), word_val (t := 1) (by norm_num),
    word_val (t := 2) (by norm_num), word_val (t := 3) (by norm_num),
    word_val (t := 4) (by norm_num), word_val (t := 5) (by norm_num)]
  rfl

theorem wb_eq : waWord = [5, 1, 5, 1, 5] ∧ wbWord = [15, 3, 11, 13, 10] := by
  refine ⟨wa_eq, ?_⟩
  unfold wbWord
  rw [waLen_eq, wbLen_eq, show wordOffset + 2 + 5 + 5 = 27712 + 6 from rfl,
    show wordOffset + 2 + 5 = 27712 + 1 from rfl,
    extract5 27712 (by simp [L_len])]
  rw [show 27712 + 1 = 27706 + 7 from rfl, show 27712 + 2 = 27706 + 8 from rfl,
    show 27712 + 3 = 27706 + 9 from rfl, show 27712 + 4 = 27706 + 10 from rfl,
    show 27712 + 5 = 27706 + 11 from rfl, word_val (t := 7) (by norm_num),
    word_val (t := 8) (by norm_num), word_val (t := 9) (by norm_num),
    word_val (t := 10) (by norm_num), word_val (t := 11) (by norm_num)]
  rfl

theorem szOK' : szOK 1365 11 = true := by decide +kernel

theorem prodA_unpack : ∀ w : List Nat, (∀ l ∈ w, l < 16) →
    CFSG.EvenSporadicStandard.G24Aut.prodA pgArrs w =
        unpack 1365 11 (w.foldr (fun l acc => pcomp 1365 11 (mask 11) (PG l) acc) (pidn 1365 11)) ∧
      canonK 1365 11 (mask 11) (1365 * 11)
        (w.foldr (fun l acc => pcomp 1365 11 (mask 11) (PG l) acc) (pidn 1365 11)) = true
  | [], _ => ⟨CFSG.KC.BfsPin.idA_eq szOK', (CFSG.KC.BfsPin.PP.id szOK').1⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := prodA_unpack w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl := h l List.mem_cons_self
    have e : CFSG.EvenSporadicStandard.G24Aut.prodA pgArrs (l :: w) =
        compA 1365 pgArrs[l]! (CFSG.EvenSporadicStandard.G24Aut.prodA pgArrs w) := rfl
    refine ⟨?_, CFSG.KC.BfsPin.canonK_pcomp (can hl) ih2⟩
    rw [e, ih1, pgArrs_get hl, CFSG.KC.BfsPin.compA_unpack (can hl) ih2]
    rfl

theorem xa_eq' : CFSG.EvenSporadicStandard.G24Aut.xa = unpack 1365 11 (LC.S 0) := by
  have h : CFSG.EvenSporadicStandard.G24Aut.xa = twoBStrong[0]! := rfl
  rw [h, CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 0 (by norm_num),
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR 0 (by norm_num))]

theorem ya_eq' : CFSG.EvenSporadicStandard.G24Aut.ya = unpack 1365 11 (LC.S 1) := by
  have h : CFSG.EvenSporadicStandard.G24Aut.ya = twoBStrong[1]! := rfl
  rw [h, CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 1 (by norm_num),
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR 1 (by norm_num))]

theorem matchOK_true : matchOK = true := by
  obtain ⟨hwa, hwb⟩ := wb_eq
  have pa := (prodA_unpack [5, 1, 5, 1, 5] (by decide)).1
  have pb := (prodA_unpack [15, 3, 11, 13, 10] (by decide)).1
  have ea : [5, 1, 5, 1, 5].foldr (fun l acc => pcomp 1365 11 (mask 11) (PG l) acc)
      (pidn 1365 11) = LC.S 0 := Nat.eq_of_beq_eq_true kWa
  have eb : [15, 3, 11, 13, 10].foldr (fun l acc => pcomp 1365 11 (mask 11) (PG l) acc)
      (pidn 1365 11) = LC.S 1 := Nat.eq_of_beq_eq_true kWb
  unfold matchOK
  rw [hwa, hwb, pa, pb, ea, eb, ← xa_eq', ← ya_eq',
    CertificateChecks.KernelCo1B.Tri2045.eqA_refl, CertificateChecks.KernelCo1B.Tri2045.eqA_refl]
  rfl

end CertificateChecks.KernelG24.Match27211
