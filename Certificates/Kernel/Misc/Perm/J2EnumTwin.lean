module

public import Certificates.Kernel.Misc.Perm.J2EnumMain
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw hx hz hI pX pZ pI cm X Z I all_of_chunks)
open CertificateChecks.KernelMisc.J2Fam
open CFSG.Monster.B.Co2 (allLt_iff)

theorem ptPerm {N G : ℕ} {GF : ℕ → ℕ} {P E R L : List ℕ}
    (h : ∀ i < N, pointK 315 9 G N GF (lget P) (EL G E) (lget R) (lget L) i = true) (i : ℕ)
    (hi : i < N) : permB 315 9 (lget P i) = true := by
  have h' := h i hi
  simp only [pointK, Bool.and_eq_true] at h'
  exact h'.1.1

theorem sqIterU (n : ℕ) : ∀ p : ℕ, permB 315 9 p = true →
    sqIterA n (unpack 315 9 p) =
        unpack 315 9
          (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q) (fun _ ih q => ih (cm q q)) n p) ∧
      permB 315 9 (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q) (fun _ ih q => ih (cm q q)) n p)
        = true := by
  induction n with
  | zero => exact fun p hp => ⟨rfl, hp⟩
  | succ n ih =>
    intro p hp
    have e : sqIterA (n + 1) (unpack 315 9 p) = sqIterA n (sqA (unpack 315 9 p)) := rfl
    rw [e, sqA, compU hp hp]
    exact ih (cm p p) (pcm hp hp)

theorem two8U {p : ℕ} (hp : permB 315 9 p = true) : isTwo8A (unpack 315 9 p) = two8K p := by
  unfold isTwo8A
  rw [(sqIterU 8 p hp).1, ← hI, eqU (sqIterU 8 p hp).2 pI]
  rfl

theorem gnaL : gensNaArr.toList = [GA 0, GA 1, H1].map (unpack 315 9) := by
  apply List.ext_getElem
  · simp [gna_size]
  · intro k h1 _
    have hk : k < 3 := by simpa [gna_size] using h1
    rw [Array.getElem_toList, ← getElem!_pos gensNaArr k (by simpa using h1), hgNa k hk]
    interval_cases k <;> rfl

theorem pNa : ∀ n ∈ [GA 0, GA 1, H1], permB 315 9 n = true := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact pGA 0 (by norm_num)
  · exact pGA 1 (by norm_num)
  · exact pH1

theorem outer0_true : (eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) xArr ||
    eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) (compA 315 xArr xArr)) = true := by
  rw [hp0, hou, hx, conjU pOU pX, conjU pP0 (pcj pOU pX), compU pX pX,
    eqU (pcj pP0 (pcj pOU pX)) pX, eqU (pcj pP0 (pcj pOU pX)) (pcm pX pX)]
  quickRfl

theorem outer_lit : (allLt cNaL.pts.size fun k =>
    !(twoTest8 gensNaArr (compA 315 cNaL.pts[k]! (compA 315 p0Arr outerArr)))) = true := by
  rw [allLt_iff, sizeNa]
  intro k hk
  have hP : ∀ i < 72, cNaL.pts[i]! = unpack 315 9 (lget NaP i) :=
    (certL_bound 72 3 NaP NaE NaR NaL).2.1
  have hp : permB 315 9 (lget NaP k) = true := ptPerm (N := 72) (all_of_chunks 72 1 ptNaS) k hk
  have pu := pcm pP0 pOU
  have pw' := pcm hp pu
  rw [hP k hk, hp0, hou, compU pP0 pOU, compU hp pu]
  unfold twoTest8
  rw [← Array.all_toList, gnaL, two8U pw',
    all_map_congr (g := fun n => two8K (cm (cm (lget NaP k) (cm P0 OU))
      (cj n (cm (lget NaP k) (cm P0 OU))))) fun n hn => by
        rw [conjU (pNa n hn) pw', compU pw' (pcj (pNa n hn) pw'),
          two8U (pcm pw' (pcj (pNa n hn) pw'))]]
  exact outAll k hk

theorem cSL0 : cSL 0 = certL 64 4 S0P S0E S0R S0L := if_pos rfl

theorem pS0 (k : ℕ) (hk : k < 64) : permB 315 9 (lget S0P k) = true :=
  ptPerm (N := 64) (all_of_chunks 64 1 ptS0S) k hk

theorem chkSCz_lit : (allLt (cSL 0).pts.size fun k =>
    !(commA (cSL 0).pts[k]! zArr) || inW 0 (cSL 0).pts[k]!) = true := by
  rw [cSL0, allLt_iff, (certL_bound 64 4 S0P S0E S0R S0L).1]
  intro k hk
  rw [(certL_bound 64 4 S0P S0E S0R S0L).2.1 k hk, hz, commU (pS0 k hk) pZ,
    inWU 0 (by norm_num) (pS0 k hk)]
  exact sczAll k hk

theorem pVE (e : ℕ) (he : e < 4) : permB 315 9 (lget VEK e) = true := by
  interval_cases e
  · exact pI
  · exact pV1
  · exact pV2
  · exact pcm pV1 pV2

theorem vEU (e : ℕ) (he : e < 4) : (if e = 0 then idA 315 else if e = 1 then v1Arr else
    if e = 2 then v2Arr else compA 315 v1Arr v2Arr) = unpack 315 9 (lget VEK e) := by
  interval_cases e
  · rw [if_pos rfl, ← hI]
    rfl
  · rw [if_neg (by decide), if_pos rfl, hv1]
    rfl
  · rw [if_neg (by decide), if_neg (by decide), if_pos rfl, hv2]
    rfl
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), hv1, hv2, compU pV1 pV2]
    rfl

theorem chkSProd_lit : (allLt (cSL 0).pts.size fun k => (wElts 0).any fun w =>
    (List.range 4).any fun e => (List.range 4).any fun f =>
      eqA 315 (cSL 0).pts[k]! (compA 315 w (compA 315
        (conjA 315 cConj[0]! (if e = 0 then idA 315 else if e = 1 then v1Arr else
          if e = 2 then v2Arr else compA 315 v1Arr v2Arr))
        (conjA 315 cConj[1]! (if f = 0 then idA 315 else if f = 1 then v1Arr else
          if f = 2 then v2Arr else compA 315 v1Arr v2Arr))))) = true := by
  rw [cSL0, allLt_iff, (certL_bound 64 4 S0P S0E S0R S0L).1]
  intro k hk
  have hp := pS0 k hk
  have c0 := pCC 0 (by norm_num)
  have c1 := pCC 1 (by norm_num)
  rw [(certL_bound 64 4 S0P S0E S0R S0L).2.1 k hk, hwe 0 (by norm_num), hcc 0 (by norm_num),
    hcc 1 (by norm_num)]
  have h := sprodAll k hk
  unfold sprodK memL SPK at h
  simp only [List.any_flatMap, List.any_map, Function.comp_def] at h
  refine Eq.trans (any_map_congr fun w hw' => any_congr_mem fun e he =>
    any_congr_mem fun f hf => ?_) h
  rw [List.mem_range] at he hf
  have pw0 := pWE 0 (by norm_num) w hw'
  rw [vEU e he, vEU f hf, conjU c0 (pVE e he), conjU c1 (pVE f hf),
    compU (pcj c0 (pVE e he)) (pcj c1 (pVE f hf)),
    compU pw0 (pcm (pcj c0 (pVE e he)) (pcj c1 (pVE f hf))),
    eqU hp (pcm pw0 (pcm (pcj c0 (pVE e he)) (pcj c1 (pVE f hf))))]

end CertificateChecks.KernelMisc.J2En

end
