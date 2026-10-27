module

public import Certificates.Kernel.Misc.Perm.J2Enum
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw hx hz hI pX pZ pI cm cz czp X Z I)
open CertificateChecks.KernelMisc.J2Fam
open CFSG.Monster.B.Co2 (allLt_iff)

theorem all_map_congr {l : List ℕ} {F : Array ℕ → Bool} {g : ℕ → Bool}
    (h : ∀ x ∈ l, F (unpack 315 9 x) = g x) : (l.map (unpack 315 9)).all F = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem any_map_congr {l : List ℕ} {F : Array ℕ → Bool} {g : ℕ → Bool}
    (h : ∀ x ∈ l, F (unpack 315 9 x) = g x) : (l.map (unpack 315 9)).any F = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem all_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem mem3 {i : ℕ} (hi : i ∈ [0, 1, 2]) : i < 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem pcm {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    permB 315 9 (cm p q) = true := permB_pcomp hw hp hq

theorem ppw {p : ℕ} (hp : permB 315 9 p = true) (e : ℕ) : permB 315 9 (pw p e) = true :=
  permB_ppow hw hp e

theorem pcj {f p : ℕ} (hf : permB 315 9 f = true) (hp : permB 315 9 p = true) :
    permB 315 9 (cj f p) = true := pcm hf (pcm hp (permB_pinvS hw hf))

theorem eqU {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    eqA 315 (unpack 315 9 p) (unpack 315 9 q) = Nat.beq p q := eqA_unpack hw hp hq

theorem compU {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    compA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cm p q) := comp_unpack hw hp hq

theorem conjU {f p : ℕ} (hf : permB 315 9 f = true) (hp : permB 315 9 p = true) :
    conjA 315 (unpack 315 9 f) (unpack 315 9 p) = unpack 315 9 (cj f p) := conj_unpack hw hf hp

theorem powU {p : ℕ} (hp : permB 315 9 p = true) (e : ℕ) :
    powArr 315 (unpack 315 9 p) e = unpack 315 9 (pw p e) := pow_unpack hw hp e

theorem commU {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    commA (unpack 315 9 p) (unpack 315 9 q) = commK p q := by
  unfold commA
  rw [compU hp hq, compU hq hp, eqU (pcm hp hq) (pcm hq hp)]
  rfl

theorem memU {l : List ℕ} (hl : ∀ w ∈ l, permB 315 9 w = true) {p : ℕ}
    (hp : permB 315 9 p = true) :
    (l.map (unpack 315 9)).any (eqA 315 (unpack 315 9 p)) = memL l p :=
  any_map_congr fun w hw' => eqU hp (hl w hw')

theorem pAE : ∀ f ∈ AEK, permB 315 9 f = true := by
  intro f hf
  simp only [AEK, List.mem_flatMap, List.mem_map, List.mem_range] at hf
  obtain ⟨a, -, c, -, rfl⟩ := hf
  exact pcm (ppw pZ a) (ppw pX c)

theorem aeU (a c : ℕ) : compA 315 (powArr 315 zArr a) (powArr 315 xArr c) =
    unpack 315 9 (cm (pw Z a) (pw X c)) := by
  rw [hz, hx, powU pZ, powU pX, compU (ppw pZ a) (ppw pX c)]

theorem hae : aElts = AEK.map (unpack 315 9) := by
  unfold aElts AEK
  simp only [aeU, List.map_flatMap, List.map_map, Function.comp_def]

theorem pWE (i : ℕ) (hi : i < 3) : ∀ w ∈ WEK i, permB 315 9 w = true := by
  intro w hw'
  simp only [WEK, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl | rfl
  · exact pI
  · exact pWG _ (by omega)
  · exact pWG _ (by omega)
  · exact pcm (pWG _ (by omega)) (pWG _ (by omega))

theorem hwe (i : ℕ) (hi : i < 3) : wElts i = (WEK i).map (unpack 315 9) := by
  unfold wElts WEK wg
  simp only [List.map_cons, List.map_nil]
  rw [← hI, hwg (2 * i + 0) (by omega), hwg (2 * i + 1) (by omega),
    compU (pWG _ (by omega)) (pWG _ (by omega))]

theorem hwgU (i j : ℕ) (h : 2 * i + j < 6) : wg i j = unpack 315 9 (WG (2 * i + j)) := hwg _ h

theorem inWU (i : ℕ) (hi : i < 3) {p : ℕ} (hp : permB 315 9 p = true) :
    inW i (unpack 315 9 p) = memL (WEK i) p := by
  unfold inW
  rw [hwe i hi, memU (pWE i hi) hp]

theorem inE0U {p : ℕ} (hp : permB 315 9 p = true) : inE 0 (unpack 315 9 p) = memL AEK p := by
  unfold inE bArr memL AEK
  rw [if_pos rfl]
  simp only [aeU, List.any_flatMap, List.any_map, Function.comp_def]
  exact any_congr_mem fun a _ => any_congr_mem fun c _ => eqU hp (pcm (ppw pZ a) (ppw pX c))

theorem involU {p : ℕ} (hp : permB 315 9 p = true) : isInvolA (unpack 315 9 p) = involK p := by
  unfold isInvolA
  rw [compU hp hp, ← hI, eqU (pcm hp hp) pI, eqU hp pI]
  rfl

@[expose] noncomputable def wAK (i : ℕ) : Bool :=
  involK (WG (2 * i + 0)) && involK (WG (2 * i + 1)) && commK (WG (2 * i + 0)) (WG (2 * i + 1)) &&
    !(Nat.beq (WG (2 * i + 0)) (WG (2 * i + 1))) && commK (WG (2 * i + 0)) Z &&
    commK (WG (2 * i + 1)) Z && (AEK.all fun f => (WEK i).all fun w => memL (WEK i) (cj f w)) &&
    ((WEK i).all fun u => Nat.beq u I ||
      ((AEK.any fun f => Nat.beq (cj f u) (WG (2 * i + 0))) &&
        (AEK.any fun f => Nat.beq (cj f u) (WG (2 * i + 1))))) &&
    ([0, 1, 2].all fun j => j == i || !(memL (WEK j) (WG (2 * i + 0))))

theorem wA0 : wAK 0 = true := by quickRfl
theorem wA1 : wAK 1 = true := by quickRfl
theorem wA2 : wAK 2 = true := by quickRfl

theorem wAU (i : ℕ) (hi : i < 3) :
    (isInvolA (wg i 0) && isInvolA (wg i 1) && commA (wg i 0) (wg i 1) &&
      !(eqA 315 (wg i 0) (wg i 1)) && commA (wg i 0) zArr && commA (wg i 1) zArr &&
      (aElts.all fun f => (wElts i).all fun w => inW i (conjA 315 f w)) &&
      ((wElts i).all fun u => eqA 315 u (idA 315) ||
        ((aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 0)) &&
          (aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 1)))) &&
      ([0, 1, 2].all fun j => j == i || !(inW j (wg i 0)))) = wAK i := by
  have p0 := pWG (2 * i + 0) (by omega)
  have p1 := pWG (2 * i + 1) (by omega)
  rw [hwgU i 0 (by omega), hwgU i 1 (by omega), involU p0, involU p1, commU p0 p1, eqU p0 p1, hz,
    commU p0 pZ, commU p1 pZ, hae, hwe i hi, ← hI]
  have e1 : ((AEK.map (unpack 315 9)).all fun f => ((WEK i).map (unpack 315 9)).all fun w =>
      inW i (conjA 315 f w)) = AEK.all fun f => (WEK i).all fun w => memL (WEK i) (cj f w) :=
    all_map_congr fun f hf => all_map_congr fun w hw' => by
      rw [conjU (pAE f hf) (pWE i hi w hw'), inWU i hi (pcj (pAE f hf) (pWE i hi w hw'))]
  have e2 : (((WEK i).map (unpack 315 9)).all fun u => eqA 315 u (unpack 315 9 I) ||
      (((AEK.map (unpack 315 9)).any fun f =>
          eqA 315 (conjA 315 f u) (unpack 315 9 (WG (2 * i + 0)))) &&
        ((AEK.map (unpack 315 9)).any fun f =>
          eqA 315 (conjA 315 f u) (unpack 315 9 (WG (2 * i + 1)))))) =
      ((WEK i).all fun u => Nat.beq u I ||
        ((AEK.any fun f => Nat.beq (cj f u) (WG (2 * i + 0))) &&
          (AEK.any fun f => Nat.beq (cj f u) (WG (2 * i + 1))))) :=
    all_map_congr fun u hu => by
      rw [eqU (pWE i hi u hu) pI,
        any_map_congr fun f hf => by rw [conjU (pAE f hf) (pWE i hi u hu),
          eqU (pcj (pAE f hf) (pWE i hi u hu)) p0],
        any_map_congr fun f hf => by rw [conjU (pAE f hf) (pWE i hi u hu),
          eqU (pcj (pAE f hf) (pWE i hi u hu)) p1]]
  have e3 : ([0, 1, 2].all fun j => j == i || !(inW j (unpack 315 9 (WG (2 * i + 0))))) =
      [0, 1, 2].all fun j => j == i || !(memL (WEK j) (WG (2 * i + 0))) :=
    all_congr_mem fun j hj => by rw [inWU j (mem3 hj) p0]
  rw [e1, e2, e3]
  rfl

theorem wBU (k : ℕ) (hk : k < 1080) :
    ((!(isInvolA cCz.pts[k]! && aElts.all fun f => commA cCz.pts[k]! (conjA 315 f cCz.pts[k]!)) ||
        inW 0 cCz.pts[k]! || inW 1 cCz.pts[k]! || inW 2 cCz.pts[k]!) &&
      [0, 1, 2].all fun i => !(commA cCz.pts[k]! (wg i 0) && commA cCz.pts[k]! (wg i 1)) ||
        inWZ i cCz.pts[k]!) = wK WEK (CertificateChecks.KernelMisc.J2C3.CzP.F k) := by
  have hp := czp k hk
  rw [cz.2.1 k hk, involU hp, inWU 0 (by norm_num) hp, inWU 1 (by norm_num) hp,
    inWU 2 (by norm_num) hp, hae,
    all_map_congr (g := fun f => commK (CertificateChecks.KernelMisc.J2C3.CzP.F k)
      (cj f (CertificateChecks.KernelMisc.J2C3.CzP.F k))) fun f hf => by
        rw [conjU (pAE f hf) hp, commU hp (pcj (pAE f hf) hp)]]
  have e : ([0, 1, 2].all fun i =>
      !(commA (unpack 315 9 (CertificateChecks.KernelMisc.J2C3.CzP.F k)) (wg i 0) &&
        commA (unpack 315 9 (CertificateChecks.KernelMisc.J2C3.CzP.F k)) (wg i 1)) ||
        inWZ i (unpack 315 9 (CertificateChecks.KernelMisc.J2C3.CzP.F k))) =
      [0, 1, 2].all fun i => !(commK (CertificateChecks.KernelMisc.J2C3.CzP.F k) (WG (2 * i + 0)) &&
        commK (CertificateChecks.KernelMisc.J2C3.CzP.F k) (WG (2 * i + 1))) ||
        (WEK i).any fun w => (List.range 3).any fun e =>
          Nat.beq (CertificateChecks.KernelMisc.J2C3.CzP.F k) (cm w (pw Z e)) :=
    all_congr_mem fun i hi => by
      have h3 := mem3 hi
      have p0 := pWG (2 * i + 0) (by omega)
      have p1 := pWG (2 * i + 1) (by omega)
      unfold inWZ
      rw [hwgU i 0 (by omega), hwgU i 1 (by omega), commU hp p0, commU hp p1, hwe i h3,
        any_map_congr fun w hw' => any_congr_mem fun e _ => by
          rw [hz, powU pZ, compU (pWE i h3 w hw') (ppw pZ e),
            eqU hp (pcm (pWE i h3 w hw') (ppw pZ e))]]
  rw [e]
  rfl

theorem chkW_true : chkW = true := by
  unfold chkW
  have hA : ([0, 1, 2].all fun i =>
      isInvolA (wg i 0) && isInvolA (wg i 1) && commA (wg i 0) (wg i 1) &&
        !(eqA 315 (wg i 0) (wg i 1)) && commA (wg i 0) zArr && commA (wg i 1) zArr &&
        (aElts.all fun f => (wElts i).all fun w => inW i (conjA 315 f w)) &&
        ((wElts i).all fun u => eqA 315 u (idA 315) ||
          ((aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 0)) &&
            (aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 1)))) &&
        ([0, 1, 2].all fun j => j == i || !(inW j (wg i 0)))) = true := by
    rw [all_congr_mem fun i hi => wAU i (mem3 hi)]
    simp only [List.all_cons, List.all_nil, wA0, wA1, wA2]
    rfl
  have hB : (allLt cCz.pts.size fun k =>
      let t := cCz.pts[k]!
      (!(isInvolA t && aElts.all fun f => commA t (conjA 315 f t)) ||
          inW 0 t || inW 1 t || inW 2 t) &&
        [0, 1, 2].all fun i => !(commA t (wg i 0) && commA t (wg i 1)) || inWZ i t) = true := by
    rw [allLt_iff, cz.1]
    intro k hk
    exact (wBU k hk).trans (wAll k hk)
  rw [hA, hB]
  rfl

theorem chkE0C_true : chkE0C = true := by
  unfold chkE0C
  rw [allLt_iff, cz.1]
  intro k hk
  have hp := czp k hk
  rw [cz.2.1 k hk, hx, commU hp pX, inE0U hp]
  exact e0cAll k hk

theorem nep (k : ℕ) (hk : k < 54) : permB 315 9 (lget NEP k) = true := by
  have h : pointK 315 9 3 54 GNE (lget NEP) (EL 3 NEE) (lget NER) (lget NEL) k = true :=
    CertificateChecks.KernelMisc.J2C3.all_of_chunks 54 1 ptNES k hk
  simp only [pointK, Bool.and_eq_true] at h
  exact h.1.1

theorem inNEL {p : ℕ} (hp : permB 315 9 p = true) :
    inCert cNEL (unpack 315 9 p) = memK 54 (lget NEP) p := by
  have b := certL_bound 54 3 NEP NEE NER NEL
  unfold inCert
  exact any_eqA_unpack hw b.1 b.2.1 nep hp

theorem chkE0N_lit : (allLt cNZ.pts.size fun k => !(inE 0 (conjA 315 cNZ.pts[k]! zArr) &&
    inE 0 (conjA 315 cNZ.pts[k]! xArr)) || inCert cNEL cNZ.pts[k]!) = true := by
  rw [allLt_iff, CertificateChecks.KernelMisc.J2C3.nz.1]
  intro k hk
  have hp := CertificateChecks.KernelMisc.J2C3.nzp k hk
  rw [CertificateChecks.KernelMisc.J2C3.nz.2.1 k hk, hz, hx, conjU hp pZ, conjU hp pX,
    inE0U (pcj hp pZ), inE0U (pcj hp pX), inNEL hp]
  exact e0nAll k hk

theorem commtU {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    commutatorA 315 (unpack 315 9 p) (unpack 315 9 q) =
      unpack 315 9 (cm (cm p q) (cm (inv p) (inv q))) := commutator_unpack hw hp hq

theorem pphi (a b c : ℕ) : permB 315 9 (phiK a b c) = true := by
  have p0 := pU4 0 (by norm_num)
  have p1 := pU4 1 (by norm_num)
  have p2 := pU4 2 (by norm_num)
  have p3 := pU4 3 (by norm_num)
  exact pcm (pcm (ppw p0 _) (ppw p1 _)) (pcm (pcm (ppw p2 _) (ppw p3 _))
    (pcm (ppw (pcm (pcm p0 p2) (pcm (permB_pinvS hw p0) (permB_pinvS hw p2))) _)
      (ppw (pcm (pcm p0 p3) (pcm (permB_pinvS hw p0) (permB_pinvS hw p3))) _)))

theorem phiKU (a b c : ℕ) : phiA a b c = unpack 315 9 (phiK a b c) := by
  have p0 := pU4 0 (by norm_num)
  have p1 := pU4 1 (by norm_num)
  have p2 := pU4 2 (by norm_num)
  have p3 := pU4 3 (by norm_num)
  have c2 : permB 315 9 (cm (cm (U4 0) (U4 2)) (cm (inv (U4 0)) (inv (U4 2)))) = true :=
    pcm (pcm p0 p2) (pcm (permB_pinvS hw p0) (permB_pinvS hw p2))
  have c3 : permB 315 9 (cm (cm (U4 0) (U4 3)) (cm (inv (U4 0)) (inv (U4 3)))) = true :=
    pcm (pcm p0 p3) (pcm (permB_pinvS hw p0) (permB_pinvS hw p3))
  unfold phiA sA tB wC
  rw [hu4 0 (by norm_num), hu4 1 (by norm_num), hu4 2 (by norm_num), hu4 3 (by norm_num),
    commtU p0 p2, commtU p0 p3, powU p0, powU p1, powU p2, powU p3, powU c2, powU c3,
    compU (ppw p0 _) (ppw p1 _), compU (ppw p2 _) (ppw p3 _), compU (ppw c2 _) (ppw c3 _),
    compU (pcm (ppw p2 _) (ppw p3 _)) (pcm (ppw c2 _) (ppw c3 _)),
    compU (pcm (ppw p0 _) (ppw p1 _)) (pcm (pcm (ppw p2 _) (ppw p3 _)) (pcm (ppw c2 _) (ppw c3 _)))]
  rfl

theorem phTeq {a b c : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4) : phT a b c = phiK a b c := by
  have h := phAll (16 * a + 4 * b + c) (by omega)
  unfold phK at h
  have e1 : (16 * a + 4 * b + c) / 16 = a := by omega
  have e2 : (16 * a + 4 * b + c) / 4 % 4 = b := by omega
  have e3 : (16 * a + 4 * b + c) % 4 = c := by omega
  rw [e1, e2, e3] at h
  exact Nat.eq_of_beq_eq_true h

theorem xor4 {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem mc4 {a b : ℕ} (ha : a < 4) (hb : b < 4) : mulCode4 a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem chkSLaw_true : chkSLaw = true := by
  unfold chkSLaw
  refine List.all_eq_true.2 fun a ha => ?_
  rw [List.mem_range] at ha
  have hl := lawAll a ha
  unfold lawK at hl
  refine Eq.trans (all_congr_mem fun b hb => all_congr_mem fun c hc =>
    all_congr_mem fun a' ha' => all_congr_mem fun b' hb' => all_congr_mem fun c' hc' => ?_) hl
  rw [List.mem_range] at hb hc ha' hb' hc'
  dsimp only
  rw [phiKU, phiKU, phiKU, compU (pphi a b c) (pphi a' b' c'),
    eqU (pcm (pphi a b c) (pphi a' b' c')) (pphi _ _ _), phTeq ha hb hc, phTeq ha' hb' hc',
    phTeq (xor4 ha ha') (xor4 hb hb') (xor4 (xor4 hc hc') (mc4 ha' hb))]

end CertificateChecks.KernelMisc.J2En

end
