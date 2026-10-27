module

public import Certificates.Kernel.SporSch.Tits.Help
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Sporadic.Tits.LocR
public import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsAbel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 1755 11 (mask 11) p

@[expose] noncomputable def wK (wd : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI wd

@[expose] noncomputable def pw (x : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1755 11) (fun _ acc => pc x acc)

@[expose] noncomputable def cmS (a b : Nat) : Nat :=
  pc (pc (pc (TitsS.SI a) (TitsS.SI b)) (TitsS.S a)) (TitsS.S b)

@[expose] noncomputable def sS (g : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0 g

@[expose] noncomputable def sR (g : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsR.LR TitsR.TRI TitsR.BP 5 0 g

theorem cc {p q : Nat} (hp : C p) (hq : C q) : C (pc p q) := canonK_pcomp hp hq

theorem cu {p q : Nat} (hp : C p) (hq : C q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  compA_unpack hp hq

theorem canSS : allN 9 (fun j => bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsS.S j),
    canonK 1755 11 (mask 11) (1755 * 11) (TitsS.SI j))) = true := by quickRfl

theorem cS {j : Nat} (hj : j < 9) : C (TitsS.S j) := ((bAnd_iff _ _).1 (allN_spec canSS j hj)).1
theorem cSI {j : Nat} (hj : j < 9) : C (TitsS.SI j) := ((bAnd_iff _ _).1 (allN_spec canSS j hj)).2
theorem canR : allN 8 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsR.S j)) = true := by
  quickRfl
theorem cR {j : Nat} (hj : j < 8) : C (TitsR.S j) := allN_spec canR j hj
theorem canId : C (pidn 1755 11) := by quickRfl
theorem idOK : idK 1755 11 (mask 11) = true := by quickRfl

theorem s_get {j : Nat} (hj : j < 9) : titsSArrs[j]! = unpack 1755 11 (TitsS.S j) :=
  bindsS.2.2.2.2.1 j hj
theorem sI_get {j : Nat} (hj : j < 9) : invCand 1755 titsSArrs[j]! = unpack 1755 11 (TitsS.SI j) := by
  rw [s_get hj]
  exact (invEqK_sound (allN_spec permS j hj)).1
theorem r_get {j : Nat} (hj : j < 8) : titsRArrs[j]! = unpack 1755 11 (TitsR.S j) :=
  bindsR.2.2.2.2.1 j hj

theorem cm_eq {a b : Nat} (ha : a < 9) (hb : b < 9) :
    commArr 1755 titsSArrs[a]! titsSArrs[b]! = unpack 1755 11 (cmS a b) := by
  unfold commArr cmS
  rw [sI_get ha, sI_get hb, s_get ha, s_get hb, cu (cSI ha) (cSI hb), cu (cc (cSI ha) (cSI hb)) (cS ha),
    cu (cc (cc (cSI ha) (cSI hb)) (cS ha)) (cS hb)]

theorem cCm {a b : Nat} (ha : a < 9) (hb : b < 9) : C (cmS a b) :=
  cc (cc (cc (cSI ha) (cSI hb)) (cS ha)) (cS hb)

theorem inS_of {g : Nat} (hg : C g) (h : sS g = true) : inS (unpack 1755 11 g) = true :=
  siftK_soundR bindsS permS TitsS.hl rfl (hi_of hg) (range_of_canonK hg) h

theorem inR_eq {g : Nat} (hg : C g) : inR (unpack 1755 11 g) = sR g :=
  siftK_eq bindsR permR TitsR.hl rfl (hi_of hg) (range_of_canonK hg)

theorem wa_eq {wd : List Int}
    (h : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd (wK wd) = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 (wK wd) :=
  (wordEqK_sound ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1⟩ permD h).1

@[expose] noncomputable def okW (wd : List Int) : Bool :=
  bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd (wK wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (wK wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (pinv (wK wd)),
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) (wK wd) (pinv (wK wd)), sS (wK wd)))))

theorem okW0 : okW [] = true := by
  unfold okW wordEqK
  quickRfl
theorem okW13 : okW [13] = true := by
  unfold okW wordEqK
  quickRfl
theorem okWY : okW [-4, 3, 3] = true := by
  unfold okW wordEqK
  quickRfl

theorem okW_spec {wd : List Int} (h : okW wd = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 (wK wd) ∧ C (wK wd) ∧ C (pinv (wK wd)) ∧
      isInvA 1755 (unpack 1755 11 (wK wd)) (invCand 1755 (unpack 1755 11 (wK wd))) = true ∧
      invCand 1755 (unpack 1755 11 (wK wd)) = unpack 1755 11 (pinv (wK wd)) ∧
      inS (unpack 1755 11 (wK wd)) = true := by
  unfold okW at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  exact ⟨wa_eq h1, h2, h3, isInv_of h4, (invEqK_sound h4).1, inS_of h2 h5⟩

@[expose] noncomputable def provK (k a b : Nat) (wd : List Int) : Bool :=
  Nat.beq (TitsR.S k) (pc (pc (pinv (wK wd)) (cmS a b)) (wK wd))

theorem pv0 : provK 0 0 1 [] = true := by quickRfl
theorem pv1 : provK 1 0 2 [] = true := by quickRfl
theorem pv2 : provK 2 0 1 [13] = true := by quickRfl

theorem prov_of {k a b : Nat} {wd : List Int} (hk : k < 8) (ha : a < 9) (hb : b < 9)
    (hw : okW wd = true) (h : provK k a b wd = true) :
    eqA 1755 titsRArrs[k]! (compA 1755 (compA 1755
      (invCand 1755 (wordArr 1755 titsDerivedArrs wd))
      (commArr 1755 titsSArrs[a]! titsSArrs[b]!)) (wordArr 1755 titsDerivedArrs wd)) = true := by
  obtain ⟨e1, c1, c2, -, e2, -⟩ := okW_spec hw
  rw [e1, e2, cm_eq ha hb, cu c2 (cCm ha hb), cu (cc c2 (cCm ha hb)) c1, r_get hk,
    eqA_unpack (cR hk) (cc (cc c2 (cCm ha hb)) c1)]
  exact h

theorem provk {k a b : Nat} {wd : List Int} (hp : titsProvenance[k]! = (a, b, wd)) (hk : k < 8)
    (ha : a < 3) (hb : b < 3) (hw : okW wd = true) (hpv : provK k a b wd = true)
    (hR : titsRWords[k]! = provWord titsSWords[a]! titsSWords[b]! wd)
    (hl : lettersOK 13 wd = true) :
    titsRWords[k]! = provWord titsSWords[titsProvenance[k]!.1]!
        titsSWords[titsProvenance[k]!.2.1]! titsProvenance[k]!.2.2 ∧
      titsProvenance[k]!.1 < 3 ∧ titsProvenance[k]!.2.1 < 3 ∧
      lettersOK 13 titsProvenance[k]!.2.2 = true ∧
      isInvA 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)
        (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true ∧
      inS (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2) = true ∧
      eqA 1755 titsRArrs[k]! (compA 1755 (compA 1755
        (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2))
        (commArr 1755 titsSArrs[titsProvenance[k]!.1]! titsSArrs[titsProvenance[k]!.2.1]!))
        (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true := by
  rw [hp]
  dsimp only
  obtain ⟨e, -, -, i, -, s⟩ := okW_spec hw
  refine ⟨hR, ha, hb, hl, ?_, ?_, prov_of hk (by omega) (by omega) hw hpv⟩
  · rw [e]
    exact i
  · rw [e]
    exact s

theorem kConj : allN 3 (fun s => allN 3 (fun r => sR (pc (pc (TitsS.S s) (TitsR.S r)) (TitsS.SI s)))) =
    true := by quickRfl
theorem kComm : allN 3 (fun a => allN 3 (fun b => sR (cmS a b))) = true := by quickRfl

@[expose] noncomputable def xy (i j : Nat) : Nat := pc (pw (wK [13]) i) (pw (wK [-4, 3, 3]) j)

theorem kXY : bAnd(sR (xy 4 0), sR (xy 0 2)) = true := by quickRfl
theorem kXYp : allN 4 (fun i => allN 2 (fun j =>
    permOK 1755 11 (mask 11) (1755 * 11) (xy i j) (pinv (xy i j)))) = true := by quickRfl
theorem kXYc : allN 4 (fun i => allN 2 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (pinv (xy i j)))) =
    true := by quickRfl
theorem kDist : allN 4 (fun i => allN 2 (fun j => allN 4 (fun i' => allN 2 (fun j' =>
    bIf(bAnd(Nat.beq i i', Nat.beq j j'), true,
      bIf(sR (pc (pinv (xy i j)) (xy i' j')), false, true)))))) = true := by quickRfl

theorem pw_eq {x : Nat} (hx : C x) : ∀ i, Nat.iterate (compA 1755 (unpack 1755 11 x)) i (idA 1755) =
    unpack 1755 11 (pw x i) ∧ C (pw x i)
  | 0 => ⟨(idK_sound idOK).symm, canId⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := pw_eq hx i
    refine ⟨?_, cc hx h2⟩
    rw [Function.iterate_succ_apply', h1, cu hx h2]
    rfl

theorem xy_eq {i j : Nat} : titsXYArr i j = unpack 1755 11 (xy i j) ∧ C (xy i j) := by
  obtain ⟨ex, -, -, -, -, -⟩ := okW_spec okW13
  obtain ⟨ey, -, -, -, -, -⟩ := okW_spec okWY
  obtain ⟨-, cx, -, -, -, -⟩ := okW_spec okW13
  obtain ⟨-, cy, -, -, -, -⟩ := okW_spec okWY
  obtain ⟨p1, q1⟩ := pw_eq cx i
  obtain ⟨p2, q2⟩ := pw_eq cy j
  refine ⟨?_, cc q1 q2⟩
  unfold titsXYArr titsXArr titsYArr
  rw [titsXWord, titsYWord, ex, ey, p1, p2, cu q1 q2]
  rfl

theorem facts : (titsSWords.length = 3 ∧ titsRWords.length = 3 ∧ titsProvenance.length = 3 ∧
      (∀ k < 3, titsRWords[k]! = provWord titsSWords[titsProvenance[k]!.1]!
        titsSWords[titsProvenance[k]!.2.1]! titsProvenance[k]!.2.2 ∧
        titsProvenance[k]!.1 < 3 ∧ titsProvenance[k]!.2.1 < 3 ∧
        lettersOK 13 titsProvenance[k]!.2.2 = true ∧
        isInvA 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)
          (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true ∧
        inS (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2) = true ∧
        eqA 1755 titsRArrs[k]! (compA 1755 (compA 1755
          (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2))
          (commArr 1755 titsSArrs[titsProvenance[k]!.1]! titsSArrs[titsProvenance[k]!.2.1]!))
          (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true) ∧
      (∀ s < 3, ∀ r < 3, inR (compA 1755 (compA 1755 titsSArrs[s]! titsRArrs[r]!)
        (invCand 1755 titsSArrs[s]!)) = true) ∧
      (∀ a < 3, ∀ b < 3, inR (commArr 1755 titsSArrs[a]! titsSArrs[b]!) = true)
    )
    ∧ (isInvA 1755 titsXArr (invCand 1755 titsXArr) = true ∧
      isInvA 1755 titsYArr (invCand 1755 titsYArr) = true ∧
      inS titsXArr = true ∧ inS titsYArr = true ∧
      inR (titsXYArr 4 0) = true ∧ inR (titsXYArr 0 2) = true ∧
      (∀ i < 4, ∀ j < 2, isInvA 1755 (titsXYArr i j) (invCand 1755 (titsXYArr i j)) = true)
    )
    ∧ ((∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2, (i, j) = (i', j') ∨
      inR (compA 1755 (invCand 1755 (titsXYArr i j)) (titsXYArr i' j')) = false)
    ) := by
  obtain ⟨e0, -, -, i0, -, s0⟩ := okW_spec okW0
  obtain ⟨e13, -, -, i13, -, s13⟩ := okW_spec okW13
  obtain ⟨eY, -, -, iY, -, sY⟩ := okW_spec okWY
  refine ⟨⟨by decide, by decide, by decide, fun k hk => ?_, fun s hs r hr => ?_,
    fun a ha b hb => ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi j hj => ?_⟩,
    fun i hi j hj i' hi' j' hj' => ?_⟩
  · interval_cases k
    · exact provk rfl (by norm_num) (by norm_num) (by norm_num) okW0 pv0 rfl rfl
    · exact provk rfl (by norm_num) (by norm_num) (by norm_num) okW0 pv1 rfl rfl
    · exact provk rfl (by norm_num) (by norm_num) (by norm_num) okW13 pv2 rfl rfl
  · rw [sI_get (by omega), s_get (by omega), r_get (by omega), cu (cS (by omega)) (cR (by omega)),
      cu (cc (cS (by omega)) (cR (by omega))) (cSI (by omega)),
      inR_eq (cc (cc (cS (by omega)) (cR (by omega))) (cSI (by omega)))]
    exact allN_spec (allN_spec kConj s hs) r hr
  · rw [cm_eq (by omega) (by omega), inR_eq (cCm (by omega) (by omega))]
    exact allN_spec (allN_spec kComm a ha) b hb
  · rw [titsXArr, titsXWord, e13]
    exact i13
  · rw [titsYArr, titsYWord, eY]
    exact iY
  · rw [titsXArr, titsXWord, e13]
    exact s13
  · rw [titsYArr, titsYWord, eY]
    exact sY
  · rw [(@xy_eq 4 0).1, inR_eq (@xy_eq 4 0).2]
    exact ((bAnd_iff (sR (xy 4 0)) (sR (xy 0 2))).1 kXY).1
  · rw [(@xy_eq 0 2).1, inR_eq (@xy_eq 0 2).2]
    exact ((bAnd_iff (sR (xy 4 0)) (sR (xy 0 2))).1 kXY).2
  · rw [xy_eq.1]
    exact isInv_of (allN_spec (allN_spec kXYp i hi) j hj)
  · have hk := allN_spec (allN_spec (allN_spec (allN_spec kDist i hi) j hj) i' hi') j' hj'
    by_cases e : (i, j) = (i', j')
    · exact Or.inl e
    · right
      obtain ⟨-, ci⟩ := @xy_eq i j
      have hinv : invCand 1755 (unpack 1755 11 (xy i j)) = unpack 1755 11 (pinv (xy i j)) :=
        (invEqK_sound (allN_spec (allN_spec kXYp i hi) j hj)).1
      have cpi : C (pinv (xy i j)) := allN_spec (allN_spec kXYc i hi) j hj
      rw [(@xy_eq i j).1, (@xy_eq i' j').1, hinv, cu cpi (@xy_eq i' j').2,
        inR_eq (cc cpi (@xy_eq i' j').2)]
      have hne : bAnd(Nat.beq i i', Nat.beq j j') = false := by
        cases h1 : Nat.beq i i' <;> cases h2 : Nat.beq j j' <;> try rfl
        exact absurd (by rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]) e
      change Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false (sR (pc (pinv (xy i j)) (xy i' j')))) true
        (bAnd(Nat.beq i i', Nat.beq j j')) = true at hk
      rw [hne] at hk
      cases h : sR (pc (pinv (xy i j)) (xy i' j'))
      · rfl
      · rw [h] at hk
        exact absurd hk (by decide)

end CertificateChecks.KernelSporSch.TitsAbel

end
