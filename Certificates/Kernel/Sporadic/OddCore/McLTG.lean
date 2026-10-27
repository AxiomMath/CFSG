module

public import Certificates.Kernel.Sporadic.OddCore.McLTF
public import Certificates.Kernel.Sporadic.OddCore.McLTKT0
public import Certificates.Kernel.Sporadic.OddCore.McLTKT1
public import Certificates.Kernel.Sporadic.OddCore.McLTKT2
public import Certificates.Kernel.Sporadic.OddCore.McLTKP0
public import Certificates.Kernel.Sporadic.OddCore.McLTKP1
public import Certificates.Kernel.Sporadic.OddCore.McLTKP2
public import Certificates.Kernel.Sporadic.OddCore.McLTKH
public import Certificates.Kernel.Sporadic.OddCore.McLTKC0
public import Certificates.Kernel.Sporadic.OddCore.McLTKC1
public import Certificates.Kernel.Sporadic.OddCore.McLTKC2
public import Certificates.Kernel.Sporadic.OddCore.McLTKC3
public import Certificates.Kernel.Sporadic.OddCore.McLTKC4
public import Certificates.Kernel.Sporadic.OddCore.McLTKC5
public import Certificates.Kernel.Sporadic.OddCore.McLTKC6
public import CFSG.Certificates.Kernel.Spor.MulHFSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelCensus
open CertificateChecks.KernelSpor

local notation "⟪" p "⟫" => tabT (unpack 275 9 p)

theorem all_rec {cnt : Nat} {T PL : Nat → Nat} {f : Table → Bool}
    (h : ∀ i < cnt, f ⟪T i⟫ = true) : (hRec 275 9 cnt T PL).1.all f = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
  simp only [hRec, Array.getElem_ofFn]
  exact h i hi'

theorem len_rec {cnt hi : Nat} {T PL : Nat → Nat} {p : Table → Bool} {q : Nat → Bool}
    (hle : cnt ≤ 64 * hi) (hq : ∀ i < cnt, p ⟪T i⟫ = q i) :
    ((hRec 275 9 cnt T PL).1.toList.filter p).length = cntBelowK cnt q hi := by
  rw [← List.countP_eq_length_filter]
  exact countP_hRec hle hq

theorem mem_at {cnt q p : Nat} {T PL : Nat → Nat} (h : atK cnt T q p = true) :
    memT 275 (hRec 275 9 cnt T PL).1 ⟪p⟫ = true := by
  unfold atK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  refine memT_of (Nat.blt_eq.mp h.1) ?_
  rw [Nat.eq_of_beq_eq_true h.2]
  exact tblEqH_self 275 _

theorem mem_atOr {cnt q p : Nat} {T PL : Nat → Nat} {e : Bool} (h : atOr cnt T q p e = true) :
    memT 275 (hRec 275 9 cnt T PL).1 ⟪p⟫ = true ∨ e = true := by
  unfold atOr at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  by_cases hq : Nat.blt q cnt = true
  · simp only [hq, ↓reduceIte] at h
    left
    refine memT_of (Nat.blt_eq.mp hq) ?_
    rw [Nat.eq_of_beq_eq_true h]
    exact tblEqH_self 275 _
  · simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
    exact Or.inr h

@[expose] noncomputable def pw (X e : Nat) : Nat := Nat.rec idP (fun _ q => pc X q) e

theorem pows (X : Nat) : Pows 275 9 X (pw X) := ⟨rfl, fun _ => rfl⟩

theorem cube_eq {p : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true) :
    tblEq 275 (powT 275 3 ⟪p⟫) (idT 275) = cube1 p := by
  rw [powT_unpack (pows p) hid hidc hp 3, hid, tblEq_unpack (pows_canon (pows p) hidc hp 3) hidc]
  rfl

theorem ord3_false {p : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true)
    (h : cube1 p = false) : ordTest 275 3 ⟪p⟫ = false := by
  rw [ordTest_unpack (pows p) hidA hidc hp 3]
  have e : Nat.beq (pw p 3) (pidn 275 9) = cube1 p := rfl
  rw [e, h, Bool.false_and]

theorem slices_of {F : Nat → Bool} {a n : Nat} (h : ∀ s < n, F (Nat.add a s) = true) :
    ∀ s, a ≤ s → s < a + n → F s = true := by
  intro s h1 h2
  have e : Nat.add a (s - a) = s := by
    change a + (s - a) = s
    omega
  have := h (s - a) (by omega)
  rwa [e] at this

theorem tAll : ∀ i < 729, tK i = true := by
  have h0 : ∀ s < 9, tSl (Nat.add 0 s) = true := fun s hs => by
    have e : Nat.add 0 s = s := Nat.zero_add s
    rw [e]
    exact tS0K.all s hs
  have h1 : ∀ s < 9, tSl (Nat.add 9 s) = true := fun s hs => tS1K.all s hs
  have h2 : ∀ s < 9, tSl (Nat.add 18 s) = true := fun s hs => tS2K.all s hs
  have hs : ∀ s < 27, tSl s = true := by
    intro s hs
    rcases Nat.lt_or_ge s 9 with g0 | g0
    · exact slices_of h0 s (by omega) (by omega)
    rcases Nat.lt_or_ge s 18 with g1 | g1
    · exact slices_of h1 s (by omega) (by omega)
    · exact slices_of h2 s (by omega) (by omega)
  intro i hi
  have h := allN_spec (hs (i / 27) (by omega)) (i % 27) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 27 (i / 27)) (i % 27) = i := by
    change 27 * (i / 27) + i % 27 = i
    omega
  rw [CFSG.KS.Raw.Orb.strictB_eq, e, CFSG.KS.Raw.Orb.bIf_eq] at h
  simpa [Nat.blt_eq.mpr hi] using h

theorem pAll : ∀ i < 243, ∀ j < 243, prK i j = true := by
  have h0 : ∀ s < 9, pSl (Nat.add 0 s) = true := fun s hs => by
    have e : Nat.add 0 s = s := Nat.zero_add s
    rw [e]
    exact pS0K.all s hs
  have h1 : ∀ s < 9, pSl (Nat.add 9 s) = true := fun s hs => pS1K.all s hs
  have h2 : ∀ s < 9, pSl (Nat.add 18 s) = true := fun s hs => pS2K.all s hs
  have hs : ∀ s < 27, pSl s = true := by
    intro s hs
    rcases Nat.lt_or_ge s 9 with g0 | g0
    · exact slices_of h0 s (by omega) (by omega)
    rcases Nat.lt_or_ge s 18 with g1 | g1
    · exact slices_of h1 s (by omega) (by omega)
    · exact slices_of h2 s (by omega) (by omega)
  intro i hi j hj
  have h := allN_spec (hs (i / 9) (by omega)) (i % 9) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 9 (i / 9)) (i % 9) = i := by
    change 9 * (i / 9) + i % 9 = i
    omega
  rw [CFSG.KS.Raw.Orb.strictB_eq, e, CFSG.KS.Raw.Orb.bIf_eq] at h
  simp only [Nat.blt_eq.mpr hi, ↓reduceIte] at h
  exact allN_spec h j hj

theorem cAll : ∀ s < 77, cSl s = true := by
  have h0 : ∀ s < 11, cSl (Nat.add 0 s) = true := fun s hs => by
    have e : Nat.add 0 s = s := Nat.zero_add s
    rw [e]
    exact cS0K.all s hs
  have h1 : ∀ s < 11, cSl (Nat.add 11 s) = true := fun s hs => cS1K.all s hs
  have h2 : ∀ s < 11, cSl (Nat.add 22 s) = true := fun s hs => cS2K.all s hs
  have h3 : ∀ s < 11, cSl (Nat.add 33 s) = true := fun s hs => cS3K.all s hs
  have h4 : ∀ s < 11, cSl (Nat.add 44 s) = true := fun s hs => cS4K.all s hs
  have h5 : ∀ s < 11, cSl (Nat.add 55 s) = true := fun s hs => cS5K.all s hs
  have h6 : ∀ s < 11, cSl (Nat.add 66 s) = true := fun s hs => cS6K.all s hs
  intro s hs
  rcases Nat.lt_or_ge s 11 with g0 | g0
  · exact slices_of h0 s (by omega) (by omega)
  rcases Nat.lt_or_ge s 22 with g1 | g1
  · exact slices_of h1 s (by omega) (by omega)
  rcases Nat.lt_or_ge s 33 with g2 | g2
  · exact slices_of h2 s (by omega) (by omega)
  rcases Nat.lt_or_ge s 44 with g3 | g3
  · exact slices_of h3 s (by omega) (by omega)
  rcases Nat.lt_or_ge s 55 with g4 | g4
  · exact slices_of h4 s (by omega) (by omega)
  rcases Nat.lt_or_ge s 66 with g5 | g5
  · exact slices_of h5 s (by omega) (by omega)
  · exact slices_of h6 s (by omega) (by omega)

theorem c_pe : ∀ i < McLTC.cnt, penumPtK 275 9 (mask 9) (275 * 9) true McLTC.G McLTC.GI 2 McLTC.cnt
    McLTC.T McLTC.PL McLTC.POS McLTC.SRT McLTC.SRI i = true := by
  intro i hi
  rw [cC] at hi
  have h := cAll (i / 400) (by omega)
  unfold cSl at h
  rw [← cC] at hi
  exact penumSl_spec h i (by change 400 * (i / 400) ≤ i; omega)
    (by change i < 400 * (i / 400) + 400; omega) hi

theorem c_hs : ∀ i < McLTC.cnt,
    hsortPtK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS McLTC.HSI i = true := by
  intro i hi
  rw [← hsortPtKF_eq]
  have hi' := hi
  rw [cC] at hi'
  have hh : ∀ s < 28, hSlF s = true := fun s hs => hSKF.all s hs
  have h := hh (i / 1100) (by omega)
  unfold hSlF at h
  exact slK_spec h i (by change 1100 * (i / 1100) ≤ i; omega)
    (by change i < 1100 * (i / 1100) + 1100; omega) hi

theorem tC' : ∀ i < McLTC.cnt, canonK 275 9 (mask 9) (275 * 9) (McLTC.T i) = true :=
  fun i hi => penumPt_canon (c_pe i hi)

theorem eC : enumClass = hRec 275 9 McLTC.cnt McLTC.T McLTC.PL ∧
    conjTreeOK 275 mclPGTbls mclPGInvTbls (threeTbl 0) (hRec 275 9 McLTC.cnt McLTC.T McLTC.PL).1
      (hRec 275 9 McLTC.cnt McLTC.T McLTC.PL).2.1 (hRec 275 9 McLTC.cnt McLTC.T McLTC.PL).2.2 =
        true ∧
    hkeysDistinct 275 (hRec 275 9 McLTC.cnt McLTC.T McLTC.PL).1.toList = true :=
  conjH_sound hn pg_tabs pgi_tabs (th_tab (by norm_num)) hdC c_pe c_hs

theorem tKe_of {i : Nat} (hi : i < 729) : tKe i (McLTT.T i) = true := by
  have h := tAll i hi
  unfold tK at h
  rwa [CFSG.KS.Raw.Orb.strictB_eq] at h

end CertificateChecks.KernelSpor.McLTK

end
